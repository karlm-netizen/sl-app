// -------------------------------------------------------------------------
//  Fehlertolerante Suche über die Schlüsselliste
//
//  Drei Stufen, absteigend nach Güte:
//    1. genauer Treffer       "ostring"   -> ostring
//    2. Wortanfang            "muhlius"   -> muhliusstr
//    3. Tippfehler (Levenshtein, gedeckelt)  "kiler" -> kieler
//
//  Getrennt indiziert wird jedes Feld mit eigenem Gewicht, damit eine
//  Straße schwerer wiegt als ein Wort aus den Bemerkungen.
// -------------------------------------------------------------------------

const GEWICHT = {
  nr:        4.0,   // Schlüsselnummer - wer sie tippt, meint genau die
  strasse:   3.0,
  hausnr:    2.5,
  /* Mitversorgte Adressen zählen fast so viel wie eigene — aber bewusst nicht
     genau gleich. Steht der Schlüssel AN der gesuchten Adresse, gehört dieser
     Datensatz nach oben; sonst entscheidet bei Gleichstand die Sortierung nach
     Nummer, und das ist Zufall. Der Abstand ist klein genug, dass ein
     mitversorgter Treffer weit vor allem anderen bleibt. */
  versorgt:  2.3,
  person:    1.6,
  ort:       1.2,
  bemerkung: 1.0,
};

// --- Normalisierung -------------------------------------------------------
// "Kieler Straße" und "Kieler Str." müssen dasselbe ergeben, sonst nützt
// die beste Tippfehler-Korrektur nichts.
const ENDUNGEN = [
  [/(strasse|str)$/, 'str'],
  [/(platz|pl)$/, 'pl'],
  [/(weg)$/, 'weg'],
];

/* 🔴 Ganze Wörter, die dasselbe bedeuten wie ihre Abkürzung in der Liste.
   99 Datensätze schreiben "Hamburger Chaussee" aus, drei kürzen zu
   "Hamburger Ch." ab — und wer den vollen Namen tippte, fand die drei
   ÜBERHAUPT NICHT. Nicht weit hinten: gar nicht. "ch" und "chaussee" liegen
   für die Tippfehler-Korrektur zu weit auseinander, und mit nur einem
   passenden Wort fiel der Datensatz unter die Schranke.

   ⚠️ Das steht bewusst NICHT bei den Endungen oben. Als Endung würde
      "(chaussee|ch)$" jedes Wort treffen, das auf "ch" endet — Biberbach,
      Hammerbusch, Friedrich, Karpfenteich: 27 Straßenwörter im Bestand.

   ℹ️ Und damit das niemand aus dem falschen Grund "repariert": die
      Endungsfassung wurde gebaut und gemessen, und sie liefert für all diese
      Wörter EXAKT dieselben Treffer. Suche und Index laufen durch dieselbe
      Normalisierung, also ist das Verstümmeln symmetrisch und hebt sich auf.
      Die Wortform steht hier nicht, weil die Endung kaputtgeht, sondern weil
      sie die Bedeutung von EINEM Wort ändert statt von 27 — bei gleichem
      Ergebnis der kleinere Eingriff. Eine Gegenprobe dafür gibt es deshalb
      nicht; sie könnte nie rot werden. */
const WORTFORMEN = new Map([
  ['chaussee', 'ch'],
]);

function normText(s) {
  return (s || '')
    .toLowerCase()
    .replace(/ä/g, 'ae').replace(/ö/g, 'oe').replace(/ü/g, 'ue')
    .replace(/ß/g, 'ss')
    .replace(/[^a-z0-9]+/g, ' ')
    .trim();
}

function tokens(s) {
  const roh = normText(s).split(' ').filter(t => t.length > 0);
  return roh.map(t => {
    if (WORTFORMEN.has(t)) return WORTFORMEN.get(t);
    for (const [muster, ersatz] of ENDUNGEN) {
      if (muster.test(t) && t.length > 4) return t.replace(muster, ersatz);
    }
    return t;
  });
}

// --- Levenshtein mit Deckel ----------------------------------------------
// Bricht ab, sobald die ganze Zeile über dem Deckel liegt: bei 15.000
// Vokabeln je Tastendruck ist das der Unterschied zwischen flüssig und zäh.
function abstand(a, b, deckel) {
  const n = a.length, m = b.length;
  if (Math.abs(n - m) > deckel) return deckel + 1;
  let vor = new Array(m + 1);
  for (let j = 0; j <= m; j++) vor[j] = j;
  for (let i = 1; i <= n; i++) {
    let akt = [i];
    let zeilenMin = i;
    for (let j = 1; j <= m; j++) {
      const kosten = a[i - 1] === b[j - 1] ? 0 : 1;
      const v = Math.min(vor[j] + 1, akt[j - 1] + 1, vor[j - 1] + kosten);
      akt[j] = v;
      if (v < zeilenMin) zeilenMin = v;
    }
    if (zeilenMin > deckel) return deckel + 1;
    vor = akt;
  }
  return vor[m];
}

/* Nur HAUSNUMMERN abwerten, nicht jede Zahl.
   ⚠️ Erst stand hier /^\d+[a-z]?$/ — damit wurde auch die Schlüsselnummer
   "02941" halbiert, und die Suche danach lieferte "Z2941" auf Platz eins:
   ein Tippfehler-Nachbar schlug den genauen Treffer. Schlüsselnummern haben
   vier oder fünf Ziffern, Hausnummern drei oder weniger. */
const HAUSNUMMER = /^\d{1,3}[a-z]?$/;

function deckelFuer(t) {
  if (t.length <= 3) return 0;
  if (t.length <= 5) return 1;
  if (t.length <= 9) return 2;
  return 3;
}

// --- Index ----------------------------------------------------------------
class Index {
  constructor(daten) {
    this.daten = daten;
    this.posting = new Map();   // token -> Map(satzId -> hoechstesGewicht)
    this.vokabular = [];
    this.nachLaenge = new Map();

    daten.forEach((r, id) => {
      this._feld(r.nr, GEWICHT.nr, id);
      // "G18" tippen und den Datensatz "G0018" finden. Im PDF stehen die
      // Verweise ohne führende Nullen, die Datensätze mit.
      if (r.nr_kanon && r.nr_kanon !== r.nr) this._feld(r.nr_kanon, GEWICHT.nr, id);
      this._feld(r.strasse, GEWICHT.strasse, id);
      this._feld(r.ort, GEWICHT.ort, id);
      this._feld(r.ansprechpartner, GEWICHT.person, id);
      this._feld(r.bemerkungen, GEWICHT.bemerkung, id);
      (r.hausnummern || []).forEach(h => this._feld(h, GEWICHT.hausnr, id));
      this._feld(r.zusatz, GEWICHT.bemerkung, id);
      (r.adressen || []).forEach(a => {
        const g = a.rolle === 'versorgt' ? GEWICHT.versorgt : GEWICHT.strasse;
        this._feld(a.strasse, g, id);
        this._feld(a.hausnummer, a.rolle === 'versorgt' ? GEWICHT.versorgt : GEWICHT.hausnr, id);
      });
      (r.passende_schluessel || []).forEach(k => this._feld(k, GEWICHT.bemerkung, id));
    });

    for (const t of this.posting.keys()) {
      this.vokabular.push(t);
      if (!this.nachLaenge.has(t.length)) this.nachLaenge.set(t.length, []);
      this.nachLaenge.get(t.length).push(t);
    }

    // 🔴 Seltenheit je Wort. Ohne das war "Kieler Str 12" kaputt: "str" steckt
    //    in rund 1.500 Straßen und "12" in hunderten Hausnummern, und beide
    //    zusammen haben gereicht, um Straßen ganz ohne "Kieler" nach oben zu
    //    tragen — 1 von 10 Treffern passte. Ein Wort, das überall vorkommt,
    //    sagt fast nichts; eines, das dreimal vorkommt, sagt alles.
    this.N = daten.length;
    this.idf = new Map();
    for (const [t, m] of this.posting) {
      let wert = Math.log(1 + this.N / m.size);
      // Eine Hausnummer allein ist keine Auskunft. Sie hilft beim Sortieren,
      // darf aber keinen Datensatz allein tragen.
      if (HAUSNUMMER.test(t)) wert *= 0.5;
      this.idf.set(t, wert);
    }
  }

  _feld(text, gewicht, id) {
    for (const t of tokens(text)) {
      let m = this.posting.get(t);
      if (!m) { m = new Map(); this.posting.set(t, m); }
      const alt = m.get(id) || 0;
      if (gewicht > alt) m.set(id, gewicht);
    }
  }

  // Alle Vokabeln, die zu einem Suchwort passen, mit Güte 0..1
  _kandidaten(q) {
    const treffer = new Map();
    if (this.posting.has(q)) treffer.set(q, 1.0);

    // Ab vier Zeichen. Bei drei war "str" ein Wortanfang von "Strande" und
    // hat damit seltene Wörter eingeschleppt, die niemand gemeint hat.
    if (q.length >= 4) {
      for (const t of this.vokabular) {
        if (t.length > q.length && t.startsWith(q)) {
          // längeres Wort, das so anfängt: "muhlius" -> "muhliusstr"
          const guete = 0.72 + 0.16 * (q.length / t.length);
          if (guete > (treffer.get(t) || 0)) treffer.set(t, guete);
        }
      }
    }

    const deckel = deckelFuer(q);
    if (deckel > 0) {
      for (let L = q.length - deckel; L <= q.length + deckel; L++) {
        const gruppe = this.nachLaenge.get(L);
        if (!gruppe) continue;
        for (const t of gruppe) {
          if (treffer.has(t)) continue;
          const d = abstand(q, t, deckel);
          if (d <= deckel) {
            const guete = 0.80 - 0.22 * d;
            if (guete > (treffer.get(t) || 0)) treffer.set(t, guete);
          }
        }
      }
    }
    return treffer;
  }

  suche(eingabe, grenze = 60) {
    const qs = tokens(eingabe);
    if (qs.length === 0) return [];

    const punkte = new Map();     // satzId -> summierte Punkte
    const getroffen = new Map();  // satzId -> wie viele Suchwörter passen

    for (const q of qs) {
      const bestesJeSatz = new Map();
      for (const [t, guete] of this._kandidaten(q)) {
        const idf = this.idf.get(t) || 0;
        for (const [id, gewicht] of this.posting.get(t)) {
          const p = guete * gewicht * idf;
          if (p > (bestesJeSatz.get(id) || 0)) bestesJeSatz.set(id, p);
        }
      }
      for (const [id, p] of bestesJeSatz) {
        punkte.set(id, (punkte.get(id) || 0) + p);
        getroffen.set(id, (getroffen.get(id) || 0) + 1);
      }
    }

    let liste = [];
    for (const [id, p] of punkte) {
      const tr = getroffen.get(id);
      liste.push({ satz: this.daten[id], punkte: p * (1 + 0.25 * (tr - 1)), treffer: tr });
    }
    liste.sort((a, b) => b.punkte - a.punkte || a.satz.nr.localeCompare(b.satz.nr));

    /* 🔴 Die Schranke, die die Liste sauber hält: weit abgeschlagene Treffer
       sind keine Antwort, sondern Rauschen. Bei "Kieler Str 12" fallen damit
       rund 800 Straßen weg, die nur eine Hausnummer 12 gemeinsam haben.

       ℹ️ Hier stand zusätzlich eine zweite Schranke ("der Datensatz muss 40 %
          des Aussagegehalts der Anfrage abdecken"). Gemessen hat sie fast
          nichts getan — 174 Treffer gegen 174, 11 gegen 11 — weil die
          Seltenheits-Gewichtung dieselben Fälle schon vorher aussortiert.
          Sie ist raus: ein Regler, der nichts regelt, sieht später wie ein
          Schutz aus, und dann verlässt sich jemand darauf. */
    if (liste.length > 1) {
      const grenzwert = liste[0].punkte * 0.28;
      liste = liste.filter(x => x.punkte >= grenzwert);
    }
    return liste.slice(0, grenze);
  }

  /* Ein Treffer je konkreter HAUSNUMMER statt je Datensatz.
     "Ostring 183, 185, 187" steht im PDF als eine Zeile, ist aber drei
     Häuser — und drei Häuser sind drei Ziele. Google Maps findet
     "Ostring 183, Kiel"; mit "Ostring 183, 185, 187, Kiel" fängt es nichts an.
     Alles andere (Schlüssel, Anzahl, Status, Ansprechpartner, Bemerkungen)
     steht in allen dreien gleich — es ist derselbe Schlüssel.

     ⚠️ Geteilt wird hier, in der ANZEIGE, nicht in den Daten. Ein Datensatz
     bleibt ein Datensatz. Sonst lägen später drei Kopien derselben Zeile in
     der Datenbank, und wer eine davon bearbeitet, hätte zwei veraltete
     daneben — beim Bearbeiten (Punkt 3 der Anforderung) wäre das genau die
     Sorte Fehler, die man erst merkt, wenn Daten schon auseinanderlaufen. */
  adressTreffer(eingabe, grenze = 60) {
    const gesucht = new Set(tokens(eingabe).filter(q => HAUSNUMMER.test(q)));
    const out = [];
    for (const t of this.suche(eingabe, grenze)) {
      /* 🔴 Aufgeteilt wird über `adressen` (Rolle "standort"), NICHT über die
         flache Liste `hausnummern`. Die weiß nichts von der Straße: hat ein
         Datensatz ZWEI Straßen — G0325, Lüdemannstr. 21,23,25 und
         Faeschstr. 30,32 —, käme dabei "Lüdemannstr. 30" heraus. Eine
         Adresse, die es nicht gibt, mit einem Google-Maps-Knopf daneben.
         Für alle 10.602 Datensätze ist das Ergebnis identisch (nachgemessen:
         die Standort-Adressen spiegeln `hausnummern` exakt) — ausdrückbar
         wird damit nur der Sonderfall. */
      const eigene = (t.satz.adressen || []).filter(a => a.rolle === 'standort');
      const alle = eigene.length ? eigene : [{
        strasse: t.satz.strasse, hausnummer: '',
        zusatz: t.satz.zusatz || '', ort: t.satz.ort || '',
      }];
      // Hat der Monteur eine Hausnummer getippt und der Datensatz hat sie,
      // zeigen wir genau die — nicht alle Nachbarhäuser dazu.
      const passend = alle.filter(a => gesucht.has((a.hausnummer || '').toLowerCase()));
      for (const a of (passend.length ? passend : alle)) {
        out.push({ satz: t.satz, punkte: t.punkte, treffer: t.treffer,
                   adresse: a, hausnummer: a.hausnummer || '' });
        if (out.length >= grenze) return out;
      }
    }
    return out;
  }
}
