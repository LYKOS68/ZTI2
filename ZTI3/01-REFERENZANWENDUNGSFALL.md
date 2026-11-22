# ZTI3 – Referenzanwendungsfall und Architekturauftrag

**Status:** Arbeitsentwurf – aus dem aktuellen Repository abgeleitet  
**Basis:** `main` von ZTI2, unverändert  
**Arbeitsbranch:** `zti3/architecture-baseline`

## 1. Entscheidung zum Referenzanwendungsfall

ZTI3 wird zuerst an einem **Gate für Ergebnisse von Coding-Agenten** entwickelt.

Ein günstiger Coding-Agent (z. B. OpenCode) bearbeitet eine klar abgegrenzte Aufgabe und liefert ein strukturiertes Ergebnis. ZTI prüft dieses Ergebnis anhand expliziter Regeln. Nur ein gültig gebundenes und freigegebenes Ergebnis darf an den nächsten Arbeitsschritt übergeben werden. Bei Ablehnung wird ein nachvollziehbarer Grund ausgegeben; der nächste Schritt erhält das Ergebnis nicht.

Dieser Anwendungsfall ist direkt im Repository angelegt:
- `idee-dashboard.jsonl`, Eintrag 27: „Gate für Agenten-Ergebnisse“.
- Eintrag 7: KI-Anbindung über freigegebene Prompts und eine Modell-Schnittstelle.
- Einträge 10 und 11: persistente Faktendatei und begrenzter Kontext.
- Eintrag 14: Rückweg für Modellantworten mit erneutem Gate.
- Eintrag 23: noch offene Portierung von `kern_3` bis `kern_5`.
- PR #2 und PR #3 untersuchen bereits die Wiederverwendung des Gates für Dokument- und Telemetrieeingaben.

Die Einträge im Dashboard sind Planungsdaten, keine Bestätigung, dass diese Funktionen bereits implementiert sind.

## 2. Konkreter Ablauf

1. **Auftrag festlegen:** Eine Aufgabe mit eindeutiger ID, erwarteten Ausgabefeldern und Prüfkriterien wird erstellt.
2. **Agent ausführen:** Ein externer Coding-Agent bearbeitet ausschließlich diesen Auftrag.
3. **Ergebnis entgegennehmen:** ZTI liest die Antwort als klar definierten Datensatz ein. Ungültige oder unvollständige Eingaben werden nicht stillschweigend repariert.
4. **Prüfen:** ZTI prüft Syntax/Struktur, Pflichtfelder, erlaubte Werte, Auftragsbezug und die für diesen Auftrag festgelegten Regeln.
5. **Gate schließen:** Das Ergebnis erhält einen eindeutigen Status. Bit 1 bedeutet: alle definierten Prüfungen bestanden und Übergabe erlaubt. Bit 0 bedeutet: abgelehnt bzw. zurückgesetzt; ein konkreter Grund ist Pflicht.
6. **Übergabe:** Nur freigegebene Ergebnisse gelangen in den nächsten Schritt. Abgelehnte Ergebnisse bleiben im Prüfprotokoll und werden nicht als akzeptierter Wissensbestand behandelt.
7. **Nachvollziehen:** Auftrag, Eingabe, Regelversion, Prüfergebnis, Grund und Ergebnis-Hash werden protokolliert.

## 3. Was der erste vertikale Durchstich beweisen muss

- Ein gültiges Agentenergebnis wird reproduzierbar angenommen.
- Fehlende Pflichtfelder, ungültige Werte und falscher Auftragsbezug werden abgelehnt.
- Bit 0 übergibt nichts an den nächsten Verarbeitungsschritt.
- Ein ungültiges Gate-Bit verändert keinen bestehenden Zustand.
- Wiederholung derselben Eingabe unter derselben Regelversion erzeugt dasselbe Prüfergebnis.
- Vorhandene Daten werden nicht unbemerkt überschrieben.
- Jeder Entscheid ist mit Eingabe, Regelversion und konkretem Grund nachvollziehbar.
- Ein Agent kann keine Prüfregeln selbst ändern oder seine eigene Freigabe erzwingen.

## 4. Abgrenzung des ersten Umfangs

**Enthalten**
- Ein klar definiertes JSONL-Eingabe- und Ausgabeformat.
- Ein deterministischer Regel- und Gate-Kern.
- Explizite Ablehnungsgründe.
- Herkunfts- und Hash-Protokoll.
- Ein externer Agent als austauschbarer Produzent.
- Automatisierte Tests mit gültigen und ungültigen Fällen.

**Nicht Teil des ersten Durchstichs**
- Eigene Programmiersprache.
- Autonomes Agenten-Netzwerk.
- Vektor-Datenbank oder semantisches Retrieval.
- Selbständernde Regeln.
- Automatische Freigabe von Code zur Ausführung oder zum Merge.
- Behauptungen über die inhaltliche Wahrheit eines Agentenergebnisses allein aufgrund eines bestandenen Struktur-Gates.

Ein bestandener Gate-Test belegt nur die ausdrücklich implementierten Regeln. Er beweist weder fachliche Richtigkeit noch Sicherheit des erzeugten Codes.

## 5. Einordnung der vorhandenen ZTI2-Basis

| Vorhandener Baustein / Beleg | Rolle im Referenzfall | Status laut bisherigem Repository-Audit |
|---|---|---|
| Zustand / One-Hot-Status | eindeutiger Prüf- und Freigabestatus | in `Main.go` vorhanden; tatsächlichen Testlauf separat bestätigen |
| Transformation / Information | Verarbeitung und Validierung | in `Main.go` vorhanden; konkrete Regeln begrenzt |
| Syncpunkt / Delta-Gate | Freigabe oder Reset | in `Main.go` vorhanden |
| Beweis 01 | reproduzierbares Lesen | Referenzdatei vorhanden; Go-Prüfpfad vorhanden |
| Beweis 02 / kern_1 | append-only Wissensbestand | Referenzdatei und Go-Prüfpfad vorhanden |
| Beweis 03 | mathematisches Lemma | eigenständige Herleitung, kein normaler Go-Check-Block |
| Beweis 04 / kern_2 | begrenzter Kontextabruf | Referenzdatei und Go-Prüfpfad vorhanden |
| Beweis 05 / kern_3 | Relevanz und Kontextaufbau | Referenzdatei vorhanden; passende Go-Implementierung im bisherigen Audit nicht gefunden |
| Beweis 06 / kern_4 | kontrollierte Modellübergabe | Referenzdatei vorhanden; passende Go-Implementierung im bisherigen Audit nicht gefunden |
| Rückweg / kern_5 | Antwort erneut einlesen und gaten | im Dashboard als offene Portierung geführt |

Diese Tabelle ist ein Ausgangsbefund, kein Ersatz für die erneute Prüfung des aktuellen Quellstands und keine Aussage, dass alle Tests ausgeführt wurden.

## 6. Architekturprinzipien für ZTI3

1. **Beweis vor Behauptung:** Konzeption, Implementierung und erfolgreich ausgeführter Test werden getrennt ausgewiesen.
2. **Kleiner Kern:** Nur Komponenten aufnehmen, die der Referenzablauf benötigt.
3. **Deterministische Grenze:** Die Freigabeentscheidung des Regelkerns muss ohne Modellinterpretation reproduzierbar sein.
4. **Modell als untrusted input:** Modellantworten sind Eingaben und müssen erneut geprüft werden.
5. **Keine implizite Persistenz:** Ein akzeptiertes Ergebnis wird nicht automatisch zur dauerhaften Wissensbasis.
6. **Append-only-Nachweis:** Bestehende Informationen und Prüfprotokolle dürfen nicht stillschweigend verändert werden.
7. **Austauschbare Adapter:** Coding-Agent und später andere Modelle bleiben außerhalb des deterministischen Kerns.
8. **Kompatibilität nur mit Nachweis:** ZTI2-Referenzen werden als Golden-Daten genutzt, soweit ihre Semantik für ZTI3 weiterhin gilt.

## 7. Nächste technische Arbeitsschritte

1. Aktuelle ZTI2-Funktionen und CLI-Modi vollständig diesem Ablauf zuordnen.
2. PR #2 und PR #3 samt Testdateien prüfen; klären, welche Experimente nur auf Branches existieren.
3. Eingabe-/Ausgabeschema für einen Agentenauftrag festlegen.
4. Akzeptanz- und Ablehnungsfälle als Golden-Testdaten definieren.
5. Erst danach die kleinste ZTI3-Komponente implementieren, die den vertikalen Durchstich ermöglicht.

## 8. Abnahmekriterium

Der erste Meilenstein ist erreicht, wenn ein Agentenergebnis über denselben reproduzierbaren Ablauf eingelesen, geprüft, mit einem begründeten Bit 0/1 abgeschlossen und nur bei Bit 1 weitergegeben wird. Alle positiven und negativen Fälle müssen automatisiert getestet sein. Bis dahin wird ZTI3 als Spezifikation bzw. Prototyp geführt, nicht als fertiges System.
