// Main.go - ZTIS-Kern: Zustand, Transformation, Information, Syncpunkt.
//
// Schritt 1: Zustand, One-Hot-Status, Invariante.
// Schritt 2: transform (Bravo), inform (Charlie), Goroutine-Stufen, Ref-Abgleich.
// Schritt 3: Gate-Tabelle Delta (Reset/Bindung) mit Post-Heal-Pruefung.
// Schritt 4: trigger, Step (Phase A, seriell), JSONL-Lauf, Golden-Replay.
// Schritt 5: Phase B (Owner-Goroutine + Bravo/Charlie-Stufen), Stress-Modus.
// Schritt 6: Engine kern_1/kern_2 (engine.py) mit B1/B3/B4 (pipeline.py),
// BEWEIS 01/02/04 gegen ref/beweis/, Gegenproben je Invariante.
// Referenz: ref/*.json (Python-Lauf loop.py).
//
// Rollen nach Position, die Namen sind nur Beschriftungen je Sicht:
//
//	Position  1          2                3            4
//	ZTIS      Zustand    Transformation   Information  Syncpunkt
//	ABCD      Alpha      Bravo            Charlie      Delta
//
// Gate-Bit 0 = Delta-Reset -> CLEAN, Gate-Bit 1 = Delta-Bindung -> UPDATED.
// Kanon und Synthese (3 Layer gleichzeitig adressierbar): kanon.json.
// Schritt 7: Prompt als 3+1 auf zwei Achsen, Gate vor jedem Modellaufruf.
// Schritt 8: Maschine: Handles (Slot + Generation), Capability-Bitset,
// Opcode-Dispatch ueber festes Array, Owner-Goroutine.
// Schritt 9: plan.py: zulaessige naechste Aufgaben aus einem Abhaengigkeits-DAG.
// Schritt 10: Zeitplanung in -plan (Dauer, Werkzeug, kritischer Pfad,
// Puffer, Claude-Grenze 30 min), -plan auch fuer idee-dashboard.jsonl.
// loop.py fuehrt die Namen um eine Position verschoben (AlphaGenerator an
// Position 2 usw.); Check-Namen und Invarianten aus ref/ behalten diese
// historischen Python-Namen, weil sie byte-genau verglichen werden.
//
//	go run Main.go                              Checks S1-S5, LAUF-A/B, STRESS gegen ref/
//	go run Main.go -lauf [-phase a|b] [-interval 0.5]
//	                                               JSONL {"t","input"} stdin -> JSONL stdout
//	go run Main.go -stress 1000                    Phase B vs. A, GOMAXPROCS {1,2,3,4,8}
//	go run Main.go -begriff WORT                   ID, Layer, Position, Bedeutung aus dem Kanon
//	go run Main.go -begriff "Zustand generieren"   fester Opcode eines Begriffspaars
//	go run Main.go -plan projects.csv              zulaessige/blockierte Aufgaben (plan.py),
//	                                               mit Spalten Dauer/Werkzeug/Status auch Zeitplan
//	go run Main.go -plan idee-dashboard.jsonl      dasselbe fuer das Ideen-Dashboard
//	go run Main.go -prompt [-aus PFAD] [-ziel PFAD]
//	                                               JSONL-Prompts stdin -> Ergebnis nach -aus,
//	                                               freigegebene Prompts nach -ziel
package main

import (
	"bytes"
	"cmp"
	"crypto/sha256"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"maps"
	"math"
	"math/bits"
	"math/rand/v2"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

// --- KANON: Positionsmodell ------------------------------------------
//
// Jeder Layer hat einen eigenen Typ. Die Position ist in allen Layern
// dieselbe (0..3, im Kanon 1..4), das Wort zeigt den Layer. Ein Operator,
// wo ein Objekt erwartet wird, kompiliert nicht.

type (
	Objekt   uint8 // ZTIS: was ist da
	Operator uint8 // ABCD: womit wird operiert
	Zoom     uint8 // Router: auf welcher Ebene (Beschriftung offen, s. kanon.json)
)

const (
	Zustand Objekt = iota
	Transformation
	Information
	Syncpunkt
)

const (
	Alpha Operator = iota
	Bravo
	Charlie
	Delta
)

var (
	objektWoerter   = [4]string{"Zustand", "Transformation", "Information", "Syncpunkt"}
	operatorWoerter = [4]string{"Alpha", "Bravo", "Charlie", "Delta"}
	// Taetigkeiten sind die Bedeutung der Operatoren, an derselben Position.
	operatorTaetigkeiten = [4]string{"identifizieren", "generieren", "validieren", "integrieren"}
)

func (o Objekt) String() string   { return objektWoerter[o&3] }
func (o Operator) String() string { return operatorWoerter[o&3] }

// Adresse spricht drei Layer gleichzeitig an, je 2 Bit, zusammen ein Byte:
// Objekt<<4 | Operator<<2 | Zoom.
type Adresse uint8

func Adr(o Objekt, op Operator, z Zoom) Adresse {
	return Adresse(o&3)<<4 | Adresse(op&3)<<2 | Adresse(z&3)
}

func (a Adresse) Objekt() Objekt     { return Objekt(a >> 4 & 3) }
func (a Adresse) Operator() Operator { return Operator(a >> 2 & 3) }
func (a Adresse) Zoom() Zoom         { return Zoom(a & 3) }

func (a Adresse) String() string {
	return fmt.Sprintf("%s/%s/Zoom%d", a.Objekt(), a.Operator(), a.Zoom()+1)
}

// --- KANON: Begriffs-Dispatcher, worst case O(1) ----------------------
//
// Jeder Begriff hat genau eine feste Stelle: Layer und Position. Richtung
// Stelle -> Begriff ist ein direkter Array-Index. Richtung Begriff -> Stelle
// ist eine perfekte Hash-Tabelle ueber das geschlossene Vokabular: ein
// FNV-1a-Hash, ein Slot, ein Vergleich, keine Kollisionskette. Der Seed
// wird beim Start gesucht und in KANON auf Kollisionsfreiheit geprueft.
// Was hier nicht steht, ist unbekannt und wird nicht geraten.

const (
	LayerObjekt uint8 = iota
	LayerOperator
	LayerRouter
	layerAnzahl
)

var (
	layerNamen    = [layerAnzahl]string{"objekt", "operator", "router"}
	layerFragen   = [layerAnzahl]string{"was ist da", "womit wird operiert", "auf welcher Ebene"}
	posBedeutung  = [4]string{"Element 1", "Element 2", "Element 3", "Motor: bindet die 3 Elemente und schliesst mit Bit 0/1 (Syncpunkt)"}
	begriffStelle = [layerAnzahl][4]string{objektWoerter, operatorWoerter, {}} // Router: Beschriftung offen
)

// Stelle ist der feste Ort eines Begriffs.
type Stelle struct {
	Begriff string
	Layer   uint8
	Pos     uint8 // 0..3
}

const dispatchBits = 5 // 32 Slots; reicht fuer bis zu 32 Begriffe

type begriffIndex struct {
	seed    uint32
	slots   [1 << dispatchBits]int8 // Index in stellen, -1 = leer
	stellen []Stelle
}

func fnv1a(seed uint32, s string) uint32 {
	h := 2166136261 ^ seed
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

// slot nimmt die oberen dispatchBits des Hashes: bei FNV haengen die
// unteren Bits nur von den unteren Bits ab (Multiplikation modulo 2^n),
// ein Seed wuerde dort kaum streuen.
func slot(seed uint32, k string) uint32 { return fnv1a(seed, k) >> (32 - dispatchBits) }

// begriffSchluessel normalisiert die Eingabe: getrimmt, klein geschrieben.
func begriffSchluessel(s string) string { return strings.ToLower(pyStrip(s)) }

// baueBegriffIndex sucht einen Seed, unter dem jeder Begriff einen eigenen
// Slot hat. Ohne solchen Seed ist das Vokabular zu gross fuer dispatchBits:
// ein Programmierfehler, daher panic beim Start.
func baueBegriffIndex() *begriffIndex {
	var st []Stelle
	for l := range layerAnzahl {
		for p, w := range begriffStelle[l] {
			if w != "" {
				st = append(st, Stelle{Begriff: w, Layer: l, Pos: uint8(p)})
			}
		}
	}
	// Taetigkeiten sind Synonyme der Operatoren: gleicher Layer, gleiche Position.
	for p, w := range operatorTaetigkeiten {
		st = append(st, Stelle{Begriff: w, Layer: LayerOperator, Pos: uint8(p)})
	}
	for seed := uint32(0); seed < 1<<16; seed++ {
		idx := &begriffIndex{seed: seed, stellen: st}
		for i := range idx.slots {
			idx.slots[i] = -1
		}
		ok := true
		for i, e := range st {
			h := slot(seed, begriffSchluessel(e.Begriff))
			if idx.slots[h] != -1 {
				ok = false
				break
			}
			idx.slots[h] = int8(i)
		}
		if ok {
			return idx
		}
	}
	panic("kanon: kein kollisionsfreier Seed fuer das Vokabular, dispatchBits erhoehen")
}

var kanonIndex = baueBegriffIndex()

// Ordne liefert die feste Stelle eines Begriffs: ein Hash, ein Slot, ein
// Vergleich.
func Ordne(begriff string) (Stelle, bool) {
	k := begriffSchluessel(begriff)
	i := kanonIndex.slots[slot(kanonIndex.seed, k)]
	if i < 0 || begriffSchluessel(kanonIndex.stellen[i].Begriff) != k {
		return Stelle{}, false
	}
	return kanonIndex.stellen[i], true
}

// taetigkeit: fuer Operatoren die Taetigkeit an ihrer Position, sonst "".
func taetigkeit(s Stelle) string {
	if s.Layer != LayerOperator {
		return ""
	}
	return operatorTaetigkeiten[s.Pos]
}

// ID ist die feste Zahl der Stelle: Layer<<2 | Pos. Synonyme an derselben
// Stelle teilen sie; sie wird nie geaendert oder neu vergeben.
func (s Stelle) ID() uint8 { return s.Layer<<2 | s.Pos }

// Opcode ist die feste Zahl eines Begriffspaars: Objekt<<2 | Operator.
type Opcode uint8

func Op(o Objekt, op Operator) Opcode { return Opcode(o&3)<<2 | Opcode(op&3) }

func (c Opcode) Objekt() Objekt     { return Objekt(c >> 2 & 3) }
func (c Opcode) Operator() Operator { return Operator(c & 3) }

// Lesart: Objekt + Taetigkeit, z.B. "Zustand generieren".
func (c Opcode) Lesart() string {
	return objektWoerter[c.Objekt()] + " " + operatorTaetigkeiten[c.Operator()]
}

// opcodeHandler: die belegten Opcodes, nur die Diagonale (gleiche Position
// in beiden Layern) hat schon Code. Alle anderen sind nicht belegt.
var opcodeHandler = [16]string{
	Opcode(Zustand)<<2 | Opcode(Alpha):        "konsistent",
	Opcode(Transformation)<<2 | Opcode(Bravo): "transform",
	Opcode(Information)<<2 | Opcode(Charlie):  "inform",
	Opcode(Syncpunkt)<<2 | Opcode(Delta):      "gate (deltaReset | deltaBinden)",
}

// GleichePosition liefert die Begriffe der anderen Layer an derselben
// Position: gleiche Stelle im Zyklus, aber nie dasselbe Wort.
func (s Stelle) GleichePosition() []string {
	out := []string{}
	for l := range layerAnzahl {
		if w := begriffStelle[l][s.Pos]; l != s.Layer && w != "" {
			out = append(out, w)
		}
	}
	return out
}

// --- 1. ZUSTAND ------------------------------------------------------

// Status ist One-Hot kodiert: ein gueltiger Status hat genau ein gesetztes Bit.
type Status uint8

const (
	Sleep Status = 1 << iota
	Wake
	Updated
	Clean
)

const validMask = Sleep | Wake | Updated | Clean

var statusNames = [...]string{"SLEEP", "WAKE", "UPDATED", "CLEAN"}

// valid: genau ein Bit gesetzt und keins ausserhalb von validMask.
func (s Status) valid() bool {
	return s != 0 && s&(s-1) == 0 && s&^validMask == 0
}

func (s Status) String() string {
	if !s.valid() {
		return "Status(" + strconv.Itoa(int(s)) + ")"
	}
	return statusNames[bits.TrailingZeros8(uint8(s))]
}

// State ist der einzige veraenderliche Zustand. HasData ersetzt Pythons None.
type State struct {
	Data      string
	HasData   bool
	Tick      int64
	LastPulse time.Duration
	Status    Status
}

func newState() State { return State{Status: Sleep} }

// konsistent ist die Zustandsinvariante. Pythons Typpruefungen auf tick und
// last_pulse erledigt hier das Typsystem; uebrig bleiben Wertebereiche.
func (s *State) konsistent() bool { return s.Tick >= 0 && s.Status.valid() }

// data liefert Data oder nil, wie Pythons state.data.
func (s *State) data() any {
	if !s.HasData {
		return nil
	}
	return s.Data
}

// --- 2. TRANSFORMATION ---------------------------------------------

// transform: nil -> "PING" (Heartbeat), alles andere unveraendert, auch 0.
func transform(raw any) any {
	if raw == nil {
		return "PING"
	}
	return raw
}

// --- 3. INFORMATION ------------------------------------------------

// Grund ist die Fehlermaske von inform; jedes gesetzte Bit ist ein
// verletztes Schema-Kriterium. Grund == 0 heisst Schema erfuellt.
type Grund uint8

const (
	GrundTyp   Grund = 1 << iota // kein string
	GrundLeer                    // getrimmt leer
	GrundBlock                   // in Blockliste
	GrundLang                    // mehr als maxLen Codepoints

	grundAlle = GrundTyp | GrundLeer | GrundBlock | GrundLang
)

const maxLen = 4096

// grundTop ist die Position des hoechsten Bits von Grund.
const grundTop = 8*unsafe.Sizeof(Grund(0)) - 1

// Compile-Zeit-Waechter fuer gateBit. Grund muss unsigned sein: bei signed
// waere ^Grund(0) == -1, und uint(-1) kompiliert nicht. Das Top-Bit darf kein
// Grund sein: sonst ist die Konstante negativ und kompiliert ebenfalls nicht.
const (
	_ = uint(^Grund(0))
	_ = ^Grund(0)>>1 - grundAlle
)

// gateBit: 1 genau dann, wenn g == 0, ohne Verzweigung. Go-Spec:
//
//	"For unsigned integer values, the operations +, -, *, and << are
//	computed modulo 2^n" -> fuer g == 0 ist g-1 == ^Grund(0), Top-Bit 1.
//	"The shift operators implement [...] logical shifts if it is an
//	unsigned integer" -> >>grundTop liefert genau das Top-Bit.
//
// Fuer 1 <= g <= grundAlle ist das Top-Bit von g-1 frei, Ergebnis 0.
// Die Waechter oben halten das bei Typwechsel (uint16, uint, ...) dicht.
func gateBit(g Grund) uint8 { return uint8((g - 1) >> grundTop) }

// pyIsSpace bildet Pythons str.isspace nach: unicode.IsSpace plus die
// Trennzeichen U+001C..U+001F, die Python als Whitespace fuehrt.
func pyIsSpace(r rune) bool { return unicode.IsSpace(r) || r >= 0x1c && r <= 0x1f }

// inform: Payload -> genau ein Bit plus Grund. Geprueft wird der getrimmte
// Wert; gebunden wird spaeter der Original-Payload.
func inform(p any) (uint8, Grund) {
	s, ok := p.(string)
	if !ok {
		return 0, GrundTyp
	}
	t := strings.TrimFunc(s, pyIsSpace)

	var g Grund
	if t == "" {
		g |= GrundLeer
	}
	switch t {
	case "INVALID", "CORRUPT":
		g |= GrundBlock
	}
	if utf8.RuneCountInString(t) > maxLen {
		g |= GrundLang
	}
	return gateBit(g), g
}

// --- Goroutine-Stufen ----------------------------------------------

// paket ist die Ausgabe von T+I fuer einen Step.
type paket struct {
	Payload any
	Bit     uint8
	Grund   Grund
}

// bravoStufe (T) und charlieStufe (I) sind reine Stufen: sie sehen nie den State.
// Ungepufferte Channels erzwingen einen Handshake pro Wert und erhalten die
// Reihenfolge. Jede Stufe schliesst ihren Ausgang, wenn der Eingang endet.
func bravoStufe(in <-chan any) <-chan any {
	out := make(chan any)
	go func() {
		defer close(out)
		for raw := range in {
			out <- transform(raw)
		}
	}()
	return out
}

func charlieStufe(in <-chan any) <-chan paket {
	out := make(chan paket)
	go func() {
		defer close(out)
		for p := range in {
			bit, g := inform(p)
			out <- paket{Payload: p, Bit: bit, Grund: g}
		}
	}()
	return out
}

// tiFunc fuehrt T und I fuer genau einen rohen Wert aus.
type tiFunc func(raw any) paket

func tiSeriell(raw any) paket {
	p := transform(raw)
	bit, g := inform(p)
	return paket{Payload: p, Bit: bit, Grund: g}
}

// tiKanal startet Bravo- und Charlie-Goroutine. Jeder ti-Aufruf schickt genau
// einen Wert hinein und holt genau ein Paket heraus; ein Aufrufer, kein
// Puffer, also strikter Handshake. stop schliesst den Eingang und wartet,
// bis beide Stufen ihren Ausgang geschlossen haben.
func tiKanal() (ti tiFunc, stop func()) {
	in := make(chan any)
	out := charlieStufe(bravoStufe(in))
	ti = func(raw any) paket {
		in <- raw
		return <-out
	}
	stop = func() {
		close(in)
		for range out {
		}
	}
	return ti, stop
}

// tiPipeline schickt rohe Eingaben durch Bravo -> Charlie, in Reihenfolge.
func tiPipeline(raws []any) []paket {
	ti, stop := tiKanal()
	defer stop()
	res := make([]paket, len(raws))
	for i, r := range raws {
		res[i] = ti(r)
	}
	return res
}

// tiParallel teilt die Schleife nach Effective Go (DoAll/DoSome) auf
// GOMAXPROCS Goroutines. T und I sind pur, jede Goroutine schreibt nur in
// ihren eigenen Indexbereich: das Ergebnis ist positionsgleich mit der
// seriellen Schleife. Der kausale Syncpunkt bleibt seriell.
func tiParallel(raws []any) []paket {
	res := make([]paket, len(raws))
	n := min(runtime.GOMAXPROCS(0), max(len(raws), 1))
	done := make(chan struct{}, n)
	for i := range n {
		go func(lo, hi int) {
			for j := lo; j < hi; j++ {
				res[j] = tiSeriell(raws[j])
			}
			done <- struct{}{}
		}(i*len(raws)/n, (i+1)*len(raws)/n)
	}
	for range n {
		<-done
	}
	return res
}

// --- 4. SYNCPUNKT ----------------------------------------------------

var (
	ErrResetFehlgeschlagen = errors.New("reset fehlgeschlagen, zustand inkonsistent")
	ErrBit                 = errors.New("gate-bit ausserhalb {0, 1}")
	ErrDeltaTyp            = errors.New("delta: payload ist kein string")
)

// Snapshot ist der Zustand vor einem Gate-Uebergang (Pythons reset_von).
type Snapshot struct {
	Data   any
	Tick   int64
	Status Status
}

func (s *State) snapshot() Snapshot {
	return Snapshot{Data: s.data(), Tick: s.Tick, Status: s.Status}
}

// deltaBinden bindet den Original-Payload, nicht den getrimmten Wert aus inform.
// Ein Nicht-string bei Bit=1 ist ein Kausalitaetsbruch: Fehler, State bleibt.
func deltaBinden(s *State, p any) (Snapshot, error) {
	d, ok := p.(string)
	if !ok {
		return Snapshot{}, fmt.Errorf("%T: %w", p, ErrDeltaTyp)
	}
	alt := s.snapshot()
	s.Data, s.HasData = d, true
	s.Status = Updated
	return alt, nil
}

// deltaReset setzt validiert auf CLEAN zurueck und heilt dabei: ein gueltiger
// Tick bleibt, ein negativer wird 0, LastPulse bleibt immer (per Typ gueltig).
// Die Post-Heal-Pruefung ist mit den heutigen Feldern unerreichbar und
// sichert kuenftige Felder ab, die deltaReset nicht heilt.
func deltaReset(s *State, _ any) (Snapshot, error) {
	alt := s.snapshot()
	s.Data, s.HasData = "", false
	if s.Tick < 0 {
		s.Tick = 0
	}
	s.Status = Clean
	if !s.konsistent() || s.HasData {
		return alt, fmt.Errorf("war %+v: %w", alt, ErrResetFehlgeschlagen)
	}
	return alt, nil
}

// gate ist die feste Zuordnung Gate-Bit -> Uebergang:
// 0 = Delta-Reset -> CLEAN, 1 = Delta-Bindung -> UPDATED.
var gate = [2]func(*State, any) (Snapshot, error){deltaReset, deltaBinden}

// syncpunkt wendet das Gate eines Pakets auf den State an. Bit > 1 wird
// nicht maskiert, sondern abgelehnt; Fehler gehen unveraendert an Step.
func syncpunkt(s *State, pk paket) (Snapshot, error) {
	if pk.Bit > 1 {
		return Snapshot{}, fmt.Errorf("%d: %w", pk.Bit, ErrBit)
	}
	return gate[pk.Bit](s, pk.Payload)
}

// --- Loop ------------------------------------------------------------

// Loop ist Pythons ChronoLoop: State plus Intervall und injizierte Uhr.
// Die Uhr liefert Zeit seit Start; im Kern gibt es kein time.Now.
// ti fuehrt T und I aus: tiSeriell in Phase A, tiKanal in Phase B. Step
// selbst ist fuer beide Phasen derselbe Code, es gibt nur eine Definition
// von korrekt.
type Loop struct {
	State    State
	Interval time.Duration
	now      func() time.Duration
	ti       tiFunc
}

func newLoop(interval time.Duration, now func() time.Duration) *Loop {
	return &Loop{State: newState(), Interval: interval, now: now, ti: tiSeriell}
}

// trigger setzt WAKE und LastPulse bei Zeitablauf oder Eingabe, sonst SLEEP.
// SLEEP ueberschreibt jeden Vorstatus, auch UPDATED und CLEAN (Quirk 2).
func (l *Loop) trigger(hasIncoming bool) bool {
	now := l.now()
	if now-l.State.LastPulse >= l.Interval || hasIncoming {
		l.State.Status = Wake
		l.State.LastPulse = now
		return true
	}
	l.State.Status = Sleep
	return false
}

// Kind ist die Art eines Step-Ergebnisses. KindReset und KindExecute liegen
// so, dass KindReset + Kind(bit) das Gate-Bit direkt abbildet.
type Kind uint8

const (
	KindSleep Kind = iota
	KindPreWake
	KindReset
	KindExecute
)

// Result ist das Ergebnis eines Steps. Bit und Grund gelten ab KindReset.
type Result struct {
	Kind  Kind
	Tick  int64
	Bit   uint8
	Grund Grund
	Data  string
}

// String liefert exakt Pythons Rueckgabetexte, data als repr.
func (r Result) String() string {
	switch r.Kind {
	case KindPreWake:
		return fmt.Sprintf("TICK %d: PRE-WAKE RESET (Zustand war inkonsistent)", r.Tick)
	case KindReset:
		return fmt.Sprintf("TICK %d: RESET (BIT=0)", r.Tick)
	case KindExecute:
		return fmt.Sprintf("TICK %d: EXECUTE (BIT=1) -> State: %s", r.Tick, pyStr(r.Data))
	}
	return "SLEEP"
}

// Step: WAKE -> Pre-Wake-Check -> Z -> T -> I -> S/Gate -> neuer Zustand.
// Der Tick steigt vor T, also auch bei RESET; beim Pre-Wake-Reset nicht.
// LastPulse ist schon in trigger gesetzt und bleibt beim Pre-Wake-Reset.
// SLEEP und Pre-Wake-Reset entstehen vor l.ti: dort laeuft nichts durch die
// Bravo/Charlie-Channels, kein Sentinel, kein leeres Paket.
func (l *Loop) Step(raw any) (Result, error) {
	if !l.trigger(raw != nil) {
		return Result{Kind: KindSleep}, nil
	}
	if !l.State.konsistent() {
		if _, err := deltaReset(&l.State, nil); err != nil {
			return Result{}, err
		}
		return Result{Kind: KindPreWake, Tick: l.State.Tick}, nil
	}

	l.State.Tick++
	pk := l.ti(raw)
	if _, err := syncpunkt(&l.State, pk); err != nil {
		return Result{}, err
	}
	return Result{
		Kind: KindReset + Kind(pk.Bit), Tick: l.State.Tick,
		Bit: pk.Bit, Grund: pk.Grund, Data: l.State.Data,
	}, nil
}

// --- Phase B: Owner-Goroutine -------------------------------------------

// schrittIn ist ein Step-Auftrag, schrittOut sein Ergebnis samt Zustand.
type schrittIn struct {
	T   float64
	Raw any
}

type schrittOut struct {
	Res    Result
	Status Status
	Tick   int64
	Err    error
}

// ownerSchritt stellt die Uhr auf s.T und fuehrt einen Step aus.
func ownerSchritt(l *Loop, now *time.Duration, s schrittIn) schrittOut {
	*now = sekunden(s.T)
	res, err := l.Step(s.Raw)
	return schrittOut{Res: res, Status: l.State.Status, Tick: l.State.Tick, Err: err}
}

// ownerStufe: Phase B. Die Owner-Goroutine haelt Loop und State exklusiv,
// T und I laufen in eigenen Goroutines hinter tiKanal. out hat genau einen
// Sender (diese Goroutine), kein select, kein default: kein Drop, feste
// Reihenfolge. Endet in, stoppt sie die Stufen und schliesst out.
func ownerStufe(in <-chan schrittIn, interval time.Duration) <-chan schrittOut {
	out := make(chan schrittOut)
	go func() {
		defer close(out)
		ti, stop := tiKanal()
		defer stop()

		var now time.Duration
		l := newLoop(interval, func() time.Duration { return now })
		l.ti = ti
		for s := range in {
			out <- ownerSchritt(l, &now, s)
		}
	}()
	return out
}

// stepper liefert die Step-Funktion einer Phase und ihr Ende.
func stepper(interval time.Duration, phase string) (step func(schrittIn) schrittOut, ende func(), err error) {
	switch phase {
	case "a":
		var now time.Duration
		l := newLoop(interval, func() time.Duration { return now })
		return func(s schrittIn) schrittOut { return ownerSchritt(l, &now, s) }, func() {}, nil
	case "b":
		in := make(chan schrittIn)
		out := ownerStufe(in, interval)
		step = func(s schrittIn) schrittOut {
			in <- s
			return <-out
		}
		ende = func() {
			close(in)
			for range out {
			}
		}
		return step, ende, nil
	}
	return nil, nil, fmt.Errorf("phase %q: erwartet a oder b", phase)
}

// --- JSONL-Lauf --------------------------------------------------------

// eingabe ist eine JSONL-Zeile. Fehlendes und null-input ergeben beide nil.
type eingabe struct {
	T     *float64 `json:"t"`
	Input any      `json:"input"`
}

// ausgabe ist eine JSONL-Ergebniszeile. bit und grund nur ab KindReset.
type ausgabe struct {
	T        float64 `json:"t"`
	Status   string  `json:"status"`
	Tick     int64   `json:"tick"`
	Bit      *uint8  `json:"bit,omitempty"`
	Grund    *uint8  `json:"grund,omitempty"`
	Ergebnis string  `json:"ergebnis"`
}

// sekunden rundet auf ganze ns: eine Float-zu-Int-Konvertierung schneidet
// laut Spec ab, 0.3*1e9 koennte sonst 1ns zu kurz werden.
func sekunden(sec float64) time.Duration { return time.Duration(math.Round(sec * 1e9)) }

// laufStream liest JSONL-Schritte, fuehrt je einen Step in der gewaehlten
// Phase aus und schreibt je eine JSONL-Zeile. Die Uhr ist das t der Zeile.
// Laeuft t rueckwaerts, bleibt die Semantik 1:1 (Python), es gibt nur eine
// Warnung auf warn.
func laufStream(r io.Reader, w, warn io.Writer, interval time.Duration, phase string) error {
	step, ende, err := stepper(interval, phase)
	if err != nil {
		return err
	}
	defer ende()

	var prevT float64
	dec := json.NewDecoder(r)
	enc := json.NewEncoder(w)
	enc.SetEscapeHTML(false)

	for i := 1; ; i++ {
		var e eingabe
		err := dec.Decode(&e)
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return fmt.Errorf("schritt %d: %w", i, err)
		}
		if e.T == nil {
			return fmt.Errorf("schritt %d: t fehlt", i)
		}
		if i > 1 && *e.T < prevT {
			fmt.Fprintf(warn, "warnung: schritt %d: t laeuft rueckwaerts (%s -> %s, delta %s)\n",
				i, pyFloat(prevT), pyFloat(*e.T), sekunden(*e.T)-sekunden(prevT))
		}
		prevT = *e.T

		so := step(schrittIn{T: *e.T, Raw: e.Input})
		if so.Err != nil {
			return fmt.Errorf("schritt %d: %w", i, so.Err)
		}
		a := ausgabe{T: *e.T, Status: so.Status.String(), Tick: so.Tick, Ergebnis: so.Res.String()}
		if so.Res.Kind >= KindReset {
			b, g := so.Res.Bit, uint8(so.Res.Grund)
			a.Bit, a.Grund = &b, &g
		}
		if err := enc.Encode(a); err != nil {
			return err
		}
	}
}

// --- 6. ENGINE: Bibliothek (kern_1, kern_2) ------------------------
//
// Port von engine.py; B1/B3/B4 stammen dort aus pipeline.py, das nicht
// vorliegt. Annahmen dazu sind an der jeweiligen Funktion markiert.

// ErrValue entspricht Pythons ValueError. Die konkrete Ursache haengt per
// %w daneben, beide sind mit errors.Is pruefbar.
var (
	ErrValue      = errors.New("value error")
	ErrDateiFehlt = errors.New("datei fehlt oder nicht lesbar")
	ErrKaputt     = errors.New("kein gueltiges UTF-8")
	ErrFaktLeer   = errors.New("neuer_fakt ist leer")
)

// kMaxZettel ist Invariante II: |aktiver Kontext| <= kMaxZettel.
const kMaxZettel = 3

// liesText ist B1: Text oder Fehler, nie "" bei fehlender oder kaputter
// Datei; leere Datei -> "". Annahme: pipeline.py liest im Textmodus mit
// newline=None, also werden \r\n und \r beim Lesen zu \n.
func liesText(pfad string) (string, error) {
	b, err := os.ReadFile(pfad)
	if err != nil {
		return "", fmt.Errorf("%w: %w: %w", ErrValue, ErrDateiFehlt, err)
	}
	if !utf8.Valid(b) {
		return "", fmt.Errorf("%s: %w: %w", pfad, ErrValue, ErrKaputt)
	}
	t := strings.ReplaceAll(string(b), "\r\n", "\n")
	return strings.ReplaceAll(t, "\r", "\n"), nil
}

// schreibeAtomar ist B3: nach Return steht text vollstaendig unter pfad.
// Temp-Datei im Zielverzeichnis, Sync, Rename, Verzeichnis-Sync. Die Rechte
// einer bestehenden Datei bleiben erhalten (CreateTemp legt 0600 an).
func schreibeAtomar(pfad, text string) (err error) {
	dir := filepath.Dir(pfad)
	f, err := os.CreateTemp(dir, "."+filepath.Base(pfad)+".tmp-*")
	if err != nil {
		return err
	}
	tmp := f.Name()
	defer func() {
		if err != nil {
			os.Remove(tmp) // Aufraeumen; der urspruengliche Fehler zaehlt
		}
	}()

	if fi, statErr := os.Stat(pfad); statErr == nil {
		if err = f.Chmod(fi.Mode().Perm()); err != nil {
			f.Close()
			return err
		}
	}
	if _, err = f.WriteString(text); err != nil {
		f.Close()
		return err
	}
	if err = f.Sync(); err != nil {
		f.Close()
		return err
	}
	if err = f.Close(); err != nil {
		return err
	}
	if err = os.Rename(tmp, pfad); err != nil {
		return err
	}
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	return d.Sync()
}

// sha256Hex ist B4: reine Funktion, 64 Hex-Zeichen ueber die UTF-8-Bytes.
func sha256Hex(text string) string {
	h := sha256.Sum256([]byte(text))
	return hex.EncodeToString(h[:])
}

// pyStrip bildet Pythons str.strip() ohne Argument nach.
func pyStrip(s string) string { return strings.TrimFunc(s, pyIsSpace) }

// pyIsLineBreak: die Trennzeichen von Pythons str.splitlines.
func pyIsLineBreak(r rune) bool {
	switch r {
	case '\n', '\v', '\f', '\r', 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029:
		return true
	}
	return false
}

// pySplitlines bildet str.splitlines() nach: \r\n ist ein Umbruch, ein
// abschliessender Umbruch erzeugt keine leere Zeile.
func pySplitlines(s string) []string {
	out := []string{}
	start := 0
	for i := 0; i < len(s); {
		r, n := utf8.DecodeRuneInString(s[i:])
		i += n
		if !pyIsLineBreak(r) {
			continue
		}
		out = append(out, s[start:i-n])
		if r == '\r' && i < len(s) && s[i] == '\n' {
			i++
		}
		start = i
	}
	if start < len(s) {
		out = append(out, s[start:])
	}
	return out
}

// pyLowerAusnahmen: Codepoints, bei denen Pythons str.lower() (volles
// Case-Mapping) von unicode.ToLower abweicht. Abgeglichen in PY-PARITAET
// gegen ref/py-lower.json ueber alle Codepoints.
var pyLowerAusnahmen = map[rune]string{0x130: "i\u0307"}

// pyLower bildet Pythons str.lower() nach, inklusive Final_Sigma.
func pyLower(s string) string {
	var b strings.Builder
	b.Grow(len(s))
	for i, r := range s {
		if r == 'Σ' {
			if finalSigma(s, i) {
				b.WriteRune('ς')
			} else {
				b.WriteRune('σ')
			}
			continue
		}
		if a, ok := pyLowerAusnahmen[r]; ok {
			b.WriteString(a)
			continue
		}
		b.WriteRune(unicode.ToLower(r))
	}
	return b.String()
}

// finalSigma: Final_Sigma-Kontext wie in CPython (handle_capital_sigma):
// \p{cased} \p{case-ignorable}* Σ !( \p{case-ignorable}* \p{cased} ).
func finalSigma(s string, i int) bool {
	vorCased := false
	for j := i; j > 0; {
		r, n := utf8.DecodeLastRuneInString(s[:j])
		j -= n
		if !caseIgnorable(r) {
			vorCased = cased(r)
			break
		}
	}
	if !vorCased {
		return false
	}
	for _, r := range s[i+len("Σ"):] {
		if !caseIgnorable(r) {
			return !cased(r)
		}
	}
	return true
}

func cased(r rune) bool {
	return unicode.In(r, unicode.Lu, unicode.Ll, unicode.Lt, unicode.Other_Lowercase, unicode.Other_Uppercase)
}

// caseIgnorable: Mn, Me, Cf, Lm, Sk sowie Word_Break MidLetter, MidNumLet
// und Single_Quote (die Word_Break-Tabelle fehlt in der Standard-Library).
func caseIgnorable(r rune) bool {
	switch r {
	case '\'', '.', ':', 0xb7, 0x387, 0x55f, 0x5f4, 0x2018, 0x2019, 0x2024, 0x2027,
		0xfe13, 0xfe52, 0xfe55, 0xff07, 0xff0e, 0xff1a:
		return true
	}
	return unicode.In(r, unicode.Mn, unicode.Me, unicode.Cf, unicode.Lm, unicode.Sk)
}

// fakten: Bibliothekstext -> Menge der Fakten (getrimmt, nicht leer).
func fakten(text string) map[string]struct{} {
	m := map[string]struct{}{}
	for _, z := range pySplitlines(text) {
		if z = pyStrip(z); z != "" {
			m[z] = struct{}{}
		}
	}
	return m
}

// faktenListe: Fakten in Bibliotheks-Reihenfolge, getrimmt, dedupliziert.
func faktenListe(text string) []string {
	gesehen := map[string]struct{}{}
	out := []string{}
	for _, z := range pySplitlines(text) {
		z = pyStrip(z)
		if _, ok := gesehen[z]; z == "" || ok {
			continue
		}
		gesehen[z] = struct{}{}
		out = append(out, z)
	}
	return out
}

// kern1 haengt neuerFakt an die Bibliothek an, falls noch nicht vorhanden.
//
//	true  = neu angehaengt, Ruecklesen bestaetigt Platte == Absicht (III)
//	false = schon vorhanden (Idempotenz) ODER Ruecklesen weicht ab
//
// Wie in Python fallen III-Verletzung und Idempotenz auf false zusammen.
func kern1(pfad, neuerFakt string) (bool, error) { return kern1Mit(pfad, neuerFakt, schreibeAtomar) }

// kern1Mit ist kern1 mit injiziertem Schreiber, fuer die Gegenproben.
func kern1Mit(pfad, neuerFakt string, schreib func(pfad, text string) error) (bool, error) {
	neuerFakt = pyStrip(neuerFakt)
	if neuerFakt == "" {
		return false, fmt.Errorf("%w: %w", ErrValue, ErrFaktLeer)
	}
	alt, err := liesText(pfad)
	if err != nil {
		return false, err
	}
	if _, ok := fakten(alt)[neuerFakt]; ok {
		return false, nil
	}

	sep := ""
	if alt != "" && !strings.HasSuffix(alt, "\n") {
		sep = "\n"
	}
	neu := alt + sep + neuerFakt + "\n"
	if err := schreib(pfad, neu); err != nil {
		return false, err
	}
	nach, err := liesText(pfad)
	if err != nil {
		return false, err
	}
	return sha256Hex(nach) == sha256Hex(neu), nil
}

// holen ist der Retrieval-Schritt: hoechstens kMaxZettel Zettel (II), bei
// jedem Aufruf neu bestimmt.
func holen(pfad, bedarf string) ([]string, error) { return holenK(pfad, bedarf, kMaxZettel) }

// holenK: Rangfolge nach Zahl getroffener Bedarfs-Woerter (Teilstring,
// case-insensitiv), bei Gleichstand Bibliotheks-Reihenfolge (stabil). Kein
// Bedarf -> leer, ohne die Datei zu lesen (wie Python).
func holenK(pfad, bedarf string, k int) ([]string, error) {
	worte := map[string]struct{}{}
	for _, w := range strings.FieldsFunc(pyLower(bedarf), pyIsSpace) {
		worte[w] = struct{}{}
	}
	if len(worte) == 0 {
		return []string{}, nil
	}
	text, err := liesText(pfad)
	if err != nil {
		return nil, err
	}

	type treffer struct {
		score int
		fakt  string
	}
	var ts []treffer
	for _, f := range faktenListe(text) {
		fl := pyLower(f)
		score := 0
		for w := range worte {
			if strings.Contains(fl, w) {
				score++
			}
		}
		if score > 0 {
			ts = append(ts, treffer{score: score, fakt: f})
		}
	}
	slices.SortStableFunc(ts, func(a, b treffer) int { return cmp.Compare(b.score, a.score) })

	out := make([]string, 0, min(len(ts), k))
	for _, t := range ts[:min(len(ts), k)] {
		out = append(out, t.fakt)
	}
	return out, nil
}

// kern2 = kern1 + holen: Bibliothek waechst, Kontext bleibt begrenzt.
func kern2(pfad, neuerFakt, bedarf string) (bool, []string, error) {
	ang, err := kern1(pfad, neuerFakt)
	if err != nil {
		return false, nil, err
	}
	kontext, err := holen(pfad, bedarf)
	if err != nil {
		return false, nil, err
	}
	return ang, kontext, nil
}

// --- 7. PROMPT: 3+1 auf zwei Achsen -----------------------------------
//
// Vertikal oben -> unten: Kopf | Koerper | Fuss. Im Koerper links -> rechts:
// genau drei Kategorien. Zwei Achsen, also zwei Motoren; das Gate ist der
// Motor vor dem Modell: erst bei Bit 1 geht der Prompt raus. Die Namen sind
// Beschriftungen, die Positionen sind fest.

type Prompt struct {
	Kopf     string     `json:"kopf"`     // oben:  Rolle, Ziel
	Koerper  [][]string `json:"koerper"`  // mitte: Kategorien links | mitte | rechts
	Fuss     string     `json:"fuss"`     // unten: Aufgabe, Antwortformat
	Herkunft []string   `json:"herkunft"` // woher jede Koerper-Zeile stammt
}

// Luecke ist die Grund-Maske eines Prompts, ein Bit je verletzter Regel.
type Luecke uint8

const (
	LueckeKopf    Luecke = 1 << iota // oben leer
	LueckeKoerper                    // keine Kategorie gefuellt
	LueckeFuss                       // unten leer
	LueckeZuViel                     // mehr als kMaxZettel Zeilen (Invariante II)
	LueckeFremd                      // Zeile ohne Herkunft, also erfunden
	LueckeAchse                      // nicht genau 3 Kategorien (Kanon 3+1)

	lueckeAlle = LueckeKopf | LueckeKoerper | LueckeFuss | LueckeZuViel | LueckeFremd | LueckeAchse
)

// Compile-Zeit-Waechter: Luecke laeuft ueber gateBit und darf dessen
// Top-Bit nicht belegen.
const _ = ^Grund(0)>>1 - Grund(lueckeAlle)

var lueckeNamen = [...]string{"kopf", "koerper", "fuss", "zu_viel", "fremd", "achse"}

// Namen liefert die gesetzten Luecken in fester Reihenfolge, nie nil.
func (l Luecke) Namen() []string {
	out := []string{}
	for i, n := range lueckeNamen {
		if l&(1<<i) != 0 {
			out = append(out, n)
		}
	}
	return out
}

// pruefe: genau ein Bit plus Maske, wie inform.
func (p Prompt) pruefe() (uint8, Luecke) {
	var l Luecke
	if pyStrip(p.Kopf) == "" {
		l |= LueckeKopf
	}
	if pyStrip(p.Fuss) == "" {
		l |= LueckeFuss
	}
	if len(p.Koerper) != 3 {
		l |= LueckeAchse
	}
	quelle := make(map[string]bool, len(p.Herkunft))
	for _, h := range p.Herkunft {
		quelle[h] = true
	}
	n := 0
	for _, kat := range p.Koerper {
		for _, z := range kat {
			n++
			if !quelle[z] {
				l |= LueckeFremd
			}
		}
	}
	if n == 0 {
		l |= LueckeKoerper
	}
	if n > kMaxZettel {
		l |= LueckeZuViel
	}
	return gateBit(Grund(l)), l
}

// Text setzt oben -> unten zusammen, im Koerper links -> rechts.
func (p Prompt) Text() string {
	var b strings.Builder
	b.WriteString(p.Kopf)
	b.WriteString("\n\n")
	for _, kat := range p.Koerper {
		for _, z := range kat {
			b.WriteString(z)
			b.WriteString("\n")
		}
	}
	b.WriteString("\n")
	b.WriteString(p.Fuss)
	return b.String()
}

// Modell ist jede Quelle, die aus einem Prompt eine Antwort macht: Stub,
// JSONL-Pipe, HTTP (net/http), lokales Programm (os/exec).
type Modell func(prompt string) (string, error)

// Motor: Bit 0 -> kein Modellaufruf, die Luecke sagt warum; Bit 1 -> Modell.
func Motor(p Prompt, m Modell) (antwort string, bit uint8, l Luecke, err error) {
	if bit, l = p.pruefe(); bit == 0 {
		return "", 0, l, nil
	}
	antwort, err = m(p.Text())
	return antwort, 1, 0, err
}

// promptAusgabe ist eine Ergebniszeile; prompt nur bei Bit 1.
type promptAusgabe struct {
	Nr         int      `json:"nr"`
	Bit        uint8    `json:"bit"`
	Luecke     []string `json:"luecke"`
	PromptHash string   `json:"prompt_hash,omitempty"`
	Prompt     string   `json:"prompt,omitempty"`
}

// promptStream liest JSONL-Prompts, schreibt je Eingabe eine Ergebniszeile
// nach aus und jeden freigegebenen Prompt zusaetzlich nach ziel (falls
// gesetzt). ziel ist der offene Anschluss fuer ein beliebiges Modell.
func promptStream(r io.Reader, aus, ziel io.Writer) error {
	dec := json.NewDecoder(r)
	encAus := json.NewEncoder(aus)
	encAus.SetEscapeHTML(false)
	var encZiel *json.Encoder
	if ziel != nil {
		encZiel = json.NewEncoder(ziel)
		encZiel.SetEscapeHTML(false)
	}

	for nr := 1; ; nr++ {
		var p Prompt
		err := dec.Decode(&p)
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return fmt.Errorf("prompt %d: %w", nr, err)
		}
		bit, l := p.pruefe()
		a := promptAusgabe{Nr: nr, Bit: bit, Luecke: l.Namen()}
		if bit == 1 {
			a.Prompt = p.Text()
			a.PromptHash = sha256Hex(a.Prompt)
			if encZiel != nil {
				if err := encZiel.Encode(map[string]any{"nr": nr, "prompt": a.Prompt, "prompt_hash": a.PromptHash}); err != nil {
					return err
				}
			}
		}
		if err := encAus.Encode(a); err != nil {
			return err
		}
	}
}

// oeffneAusgabe: "-" ist stdout, sonst wird an die Datei (oder FIFO)
// angehaengt und sie bei Bedarf angelegt.
func oeffneAusgabe(pfad string) (io.WriteCloser, error) {
	if pfad == "-" {
		return nopCloser{os.Stdout}, nil
	}
	return os.OpenFile(pfad, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0o644)
}

type nopCloser struct{ io.Writer }

func (nopCloser) Close() error { return nil }

// --- 8. MASCHINE: Handles, Dispatcher, Owner ----------------------------
//
// Komplexitaet je Pfad, worst case:
//
//	Neu / Frei    O(1)  Free-Stack ueber festes Array, kein Scan
//	Lookup        O(1)  Array-Index + Generationsvergleich
//	Capability    O(1)  ein AND auf uint16, ein Bit je Opcode
//	Dispatch      O(1)  Array-Index in handlers; die Handler selbst kosten
//	                    transform O(1), inform O(len(payload)), gate O(1)
//	Queue         Channel: Send/Recv O(1), ungepuffert = Backpressure
//
// Veraltete Handles werden nicht uebersprungen, sondern bekommen ein
// Ergebnis mit Abweisung stale: jede Msg hat genau ein Ergebnis, kein Drop.

const maxObjekte = 256

// Handle ist die echte Laufzeit-ID eines Objekts. Gen 0 ist nie gueltig.
type Handle struct {
	Slot uint16
	Gen  uint32
}

type objektSlot struct {
	gen     uint32
	belegt  bool
	caps    uint16 // Bit c: Opcode c darf auf dieses Objekt wirken
	state   State
	payload any   // aus generieren
	info    paket // aus validieren, verbraucht von integrieren
	hatInfo bool
}

var ErrVoll = errors.New("maschine: keine freien Slots")

// Maschine haelt alle Objekte. Neu und Frei nur ausserhalb von Lauf, im
// Lauf greift ausschliesslich die Owner-Goroutine auf die Slots zu.
type Maschine struct {
	slots   [maxObjekte]objektSlot
	frei    [maxObjekte]uint16
	freiTop int
}

func neueMaschine() *Maschine {
	m := &Maschine{freiTop: maxObjekte}
	for i := range m.frei {
		m.frei[i] = uint16(maxObjekte - 1 - i) // Slot 0 wird zuerst vergeben
	}
	return m
}

// Neu belegt einen Slot mit frischem Zustand und den erlaubten Opcodes.
func (m *Maschine) Neu(caps uint16) (Handle, error) {
	if m.freiTop == 0 {
		return Handle{}, ErrVoll
	}
	m.freiTop--
	i := m.frei[m.freiTop]
	s := &m.slots[i]
	*s = objektSlot{gen: s.gen + 1, belegt: true, caps: caps, state: newState()}
	return Handle{Slot: i, Gen: s.gen}, nil
}

// Frei macht jeden alten Handle sofort ungueltig. Ein Slot, dessen
// Generation am Ende ist, wird stillgelegt statt wiederverwendet: kein
// ABA nach Ueberlauf.
func (m *Maschine) Frei(h Handle) bool {
	s, ok := m.slot(h)
	if !ok {
		return false
	}
	s.belegt = false
	s.gen++
	if s.gen != math.MaxUint32 {
		m.frei[m.freiTop] = h.Slot
		m.freiTop++
	}
	return true
}

func (m *Maschine) slot(h Handle) (*objektSlot, bool) {
	if int(h.Slot) >= maxObjekte || h.Gen == 0 {
		return nil, false
	}
	s := &m.slots[h.Slot]
	return s, s.belegt && s.gen == h.Gen
}

// Abweisung: warum die Maschine eine Msg nicht an einen Handler gibt.
type Abweisung uint8

const (
	AbwStale       Abweisung = 1 << iota // Handle veraltet oder nie vergeben
	AbwOpcode                            // Opcode ausserhalb 0..15
	AbwVerboten                          // Capability fehlt
	AbwNichtBelegt                       // Opcode hat noch keine Bedeutung im Code
	AbwOhneInfo                          // integrieren ohne vorheriges validieren
	AbwFehler                            // Handler meldet einen Fehler
)

type Msg struct {
	Op  Opcode
	H   Handle
	Arg any
}

// Ergebnis: genau eins je Msg. Bit 0 ohne Abweisung ist ein regulaeres
// Gate-Ergebnis, Bit 0 mit Abweisung heisst, der Handler lief nicht.
type Ergebnis struct {
	Op        Opcode
	H         Handle
	Bit       uint8
	Abweisung Abweisung
	Grund     Grund
	Err       error
}

type handler func(s *objektSlot, arg any) Ergebnis

// handlers: jeder der 16 Opcodes hat einen Eintrag. Belegt ist nur die
// Diagonale, alle anderen weisen mit AbwNichtBelegt ab, bis ihre Bedeutung
// festgelegt ist.
var handlers = func() (t [16]handler) {
	for i := range t {
		t[i] = hNichtBelegt
	}
	t[Op(Zustand, Alpha)] = hIdentifiziere
	t[Op(Transformation, Bravo)] = hGeneriere
	t[Op(Information, Charlie)] = hValidiere
	t[Op(Syncpunkt, Delta)] = hIntegriere
	return t
}()

func hNichtBelegt(*objektSlot, any) Ergebnis { return Ergebnis{Abweisung: AbwNichtBelegt} }

// Zustand identifizieren: Bit 1 genau dann, wenn die Invariante haelt.
func hIdentifiziere(s *objektSlot, _ any) Ergebnis {
	if s.state.konsistent() {
		return Ergebnis{Bit: 1}
	}
	return Ergebnis{}
}

// Transformation generieren: Payload aus roher Eingabe; alte Info verfaellt.
func hGeneriere(s *objektSlot, raw any) Ergebnis {
	s.payload, s.hatInfo = transform(raw), false
	return Ergebnis{Bit: 1}
}

// Information validieren: genau ein Bit plus Grund, gemerkt fuer integrieren.
func hValidiere(s *objektSlot, _ any) Ergebnis {
	bit, g := inform(s.payload)
	s.info, s.hatInfo = paket{Payload: s.payload, Bit: bit, Grund: g}, true
	return Ergebnis{Bit: bit, Grund: g}
}

// Syncpunkt integrieren: das gemerkte Bit ueber das Gate binden (1) oder
// zuruecksetzen (0). Danach ist die Info verbraucht.
func hIntegriere(s *objektSlot, _ any) Ergebnis {
	if !s.hatInfo {
		return Ergebnis{Abweisung: AbwOhneInfo}
	}
	pk := s.info
	s.payload, s.hatInfo = nil, false
	if _, err := syncpunkt(&s.state, pk); err != nil {
		return Ergebnis{Abweisung: AbwFehler, Err: err}
	}
	return Ergebnis{Bit: pk.Bit, Grund: pk.Grund}
}

// Dispatch: Handle -> Generation -> Opcode-Grenze -> Capability -> Handler.
func (m *Maschine) Dispatch(msg Msg) Ergebnis {
	e := Ergebnis{Op: msg.Op, H: msg.H}
	s, ok := m.slot(msg.H)
	switch {
	case !ok:
		e.Abweisung = AbwStale
	case msg.Op > 15:
		e.Abweisung = AbwOpcode
	case s.caps&(1<<msg.Op) == 0:
		e.Abweisung = AbwVerboten
	default:
		e = handlers[msg.Op](s, msg.Arg)
		e.Op, e.H = msg.Op, msg.H
	}
	return e
}

// Lauf: Owner-Goroutine, einziger Zugriff auf die Slots; genau ein
// Ergebnis je Msg, in Reihenfolge.
func (m *Maschine) Lauf(in <-chan Msg) <-chan Ergebnis {
	out := make(chan Ergebnis)
	go func() {
		defer close(out)
		for msg := range in {
			out <- m.Dispatch(msg)
		}
	}()
	return out
}

// --- 9. PLAN: zulaessige naechste Aufgaben (plan.py) -------------------
//
// Port von plan.py, Ausgabe byte-gleich (ref/plan-faelle.json). Jede Aufgabe
// ist ein Gate: Bit 1 (zulaessig) genau dann, wenn alle Abhaengigkeiten
// FERTIG sind. Python-Eigenheiten bleiben: doppelte IDs werden still
// zusammengelegt (die letzte Zeile gewinnt im Graph), ein BOM vor dem Kopf
// macht die Spalte ID unauffindbar.

// planStatus ist wie in plan.py fest verdrahtet; nicht genannte IDs = OFFEN.
var planStatus = map[string]string{"P1": "FERTIG"}

const planWurzel = "Start"

// planSpalten in sortierter Reihenfolge, wie Pythons sorted(fehlend).
var planSpalten = []string{"Abhängigkeit", "Aufgabe", "ID"}

type planAufgabe struct {
	ID, Aufgabe string
	Deps        []string
	Dauer       float64 // in Sitzungen; nur mit Spalte Dauer
	Werkzeug    string  // claude | opencode | antigravity | manus | roman | ""
	Status      string  // "" = aus planStatus
}

// planDatei: die Aufgaben plus welche optionalen Spalten es gab. Ohne
// Dauer und Status ist die Ausgabe byte-gleich mit plan.py.
type planDatei struct {
	Zeilen    []planAufgabe
	HatDauer  bool
	HatStatus bool
}

// Zeitbudget aus profil.json (PLAN prueft die Gleichheit): eine Sitzung mit
// einer CLI dauert 45 min, eine Claude-Sitzung hoechstens 30 min.
const (
	sitzungMinuten       = 45
	claudeSitzungMinuten = 30
	claudeMaxSitzungen   = 1
	wocheMinStunden      = 48
	wocheMaxStunden      = 72
)

var planWerkzeuge = []string{"claude", "opencode", "antigravity", "manus", "roman"}

var planStatusWerte = []string{"OFFEN", "LAEUFT", "FERTIG"}

// dauerSekunden: Dauer in ganzen Sekunden; Claude-Sitzungen zaehlen 30 min,
// alle anderen 45 min. Ganze Sekunden halten die Puffer-Rechnung exakt.
func (a planAufgabe) dauerSekunden() int64 {
	m := float64(sitzungMinuten)
	if a.Werkzeug == "claude" {
		m = claudeSitzungMinuten
	}
	return int64(math.Round(a.Dauer * m * 60))
}

type planBlockade struct {
	A       planAufgabe
	Fehlend []string
}

// parseDeps: "P1.3/P1.4" -> [P1.3 P1.4]; "Start" -> [].
func parseDeps(feld string) []string {
	out := []string{}
	for _, t := range strings.Split(feld, "/") {
		if t = pyStrip(t); t != "" && t != planWurzel {
			out = append(out, t)
		}
	}
	return out
}

// parseZeilen ist B2: Text -> Aufgaben, Leer- und Trennzeilen raus.
// LazyQuotes und variable Feldzahl entsprechen Pythons csv-Defaults.
// Optionale Spalten: Dauer (Sitzungen, Komma oder Punkt), Werkzeug, Status.
func parseZeilen(text string) (planDatei, error) {
	r := csv.NewReader(strings.NewReader(text))
	r.FieldsPerRecord = -1
	r.LazyQuotes = true
	kopf, err := r.Read()
	gefunden := "None"
	idx := map[string]int{}
	switch {
	case err == io.EOF:
	case err != nil:
		return planDatei{}, fmt.Errorf("%w: %w", ErrValue, err)
	default:
		gefunden = pyRepr(kopf)
		for i, k := range kopf {
			idx[k] = i // wie DictReader: bei doppeltem Kopf gewinnt die letzte Spalte
		}
	}
	var fehlend []string
	for _, sp := range planSpalten {
		if _, ok := idx[sp]; !ok {
			fehlend = append(fehlend, sp)
		}
	}
	if len(fehlend) > 0 {
		return planDatei{}, fmt.Errorf("CSV-Kopf unvollstaendig, fehlt: %s. Gefunden: %s: %w",
			strings.Join(fehlend, ", "), gefunden, ErrValue)
	}
	_, hatDauer := idx["Dauer"]
	_, hatStatus := idx["Status"]

	feld := func(rec []string, sp string) string {
		if i, ok := idx[sp]; ok && i < len(rec) { // fehlende Spalte = leer, nie Spalte 0
			return rec[i]
		}
		return ""
	}
	var zs []planAufgabe
	for {
		rec, err := r.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			return planDatei{}, fmt.Errorf("%w: %w", ErrValue, err)
		}
		id := pyStrip(feld(rec, "ID"))
		if id == "" {
			continue // Trennzeile
		}
		a := planAufgabe{ID: id, Aufgabe: pyStrip(feld(rec, "Aufgabe")), Deps: parseDeps(feld(rec, "Abhängigkeit"))}
		if hatDauer {
			if a.Dauer, err = parseDauer(feld(rec, "Dauer")); err != nil {
				return planDatei{}, fmt.Errorf("%s: %w", id, err)
			}
		}
		if err := setzeWerkzeugStatus(&a, feld(rec, "Werkzeug"), feld(rec, "Status")); err != nil {
			return planDatei{}, err
		}
		zs = append(zs, a)
	}
	if len(zs) == 0 {
		return planDatei{}, fmt.Errorf("keine Aufgaben gelesen - CSV leer oder Format falsch: %w", ErrValue)
	}
	return planDatei{Zeilen: zs, HatDauer: hatDauer, HatStatus: hatStatus}, nil
}

// parseDauer: Sitzungen, leer = 0, Komma oder Punkt; negativ ist ein Fehler.
func parseDauer(feld string) (float64, error) {
	t := strings.ReplaceAll(pyStrip(feld), ",", ".")
	if t == "" {
		return 0, nil
	}
	d, err := strconv.ParseFloat(t, 64)
	if err != nil || d < 0 || math.IsInf(d, 0) || math.IsNaN(d) {
		return 0, fmt.Errorf("Dauer '%s' ist keine Zahl >= 0 (Sitzungen): %w", feld, ErrValue)
	}
	return d, nil
}

// setzeWerkzeugStatus prueft Werkzeug und Status gegen die festen Listen.
func setzeWerkzeugStatus(a *planAufgabe, werkzeug, status string) error {
	a.Werkzeug = strings.ToLower(pyStrip(werkzeug))
	if a.Werkzeug != "" && !slices.Contains(planWerkzeuge, a.Werkzeug) {
		return fmt.Errorf("%s: Werkzeug '%s' unbekannt (erlaubt: %s): %w", a.ID, werkzeug, strings.Join(planWerkzeuge, ", "), ErrValue)
	}
	a.Status = strings.ToUpper(pyStrip(status))
	if a.Status != "" && !slices.Contains(planStatusWerte, a.Status) {
		return fmt.Errorf("%s: Status '%s' unbekannt (erlaubt: %s): %w", a.ID, status, strings.Join(planStatusWerte, ", "), ErrValue)
	}
	return nil
}

// ladeDashboard liest idee-dashboard.jsonl als Aufgaben: ID = I<id>,
// abhaengig = Liste von ids, status nutzbar/erledigt = FERTIG, laeuft =
// LAEUFT, sonst OFFEN.
func ladeDashboard(text string) (planDatei, error) {
	dec := json.NewDecoder(strings.NewReader(text))
	var zs []planAufgabe
	for n := 1; ; n++ {
		var e struct {
			ID        int      `json:"id"`
			Titel     string   `json:"titel"`
			Status    string   `json:"status"`
			Abhaengig []int    `json:"abhaengig"`
			Dauer     *float64 `json:"dauer"`
			Werkzeug  string   `json:"werkzeug"`
		}
		if err := dec.Decode(&e); err == io.EOF {
			break
		} else if err != nil {
			return planDatei{}, fmt.Errorf("zeile %d: %w: %w", n, ErrValue, err)
		}
		a := planAufgabe{ID: fmt.Sprintf("I%d", e.ID), Aufgabe: e.Titel, Deps: []string{}}
		for _, d := range e.Abhaengig {
			a.Deps = append(a.Deps, fmt.Sprintf("I%d", d))
		}
		if e.Dauer != nil {
			if *e.Dauer < 0 {
				return planDatei{}, fmt.Errorf("%s: Dauer < 0: %w", a.ID, ErrValue)
			}
			a.Dauer = *e.Dauer
		}
		st := "OFFEN"
		switch e.Status {
		case "nutzbar", "erledigt":
			st = "FERTIG"
		case "laeuft":
			st = "LAEUFT"
		}
		if err := setzeWerkzeugStatus(&a, e.Werkzeug, st); err != nil {
			return planDatei{}, err
		}
		zs = append(zs, a)
	}
	if len(zs) == 0 {
		return planDatei{}, fmt.Errorf("keine Aufgaben gelesen - Dashboard leer: %w", ErrValue)
	}
	return planDatei{Zeilen: zs, HatDauer: true, HatStatus: true}, nil
}

// pruefeGraph: fehlende Abhaengigkeiten und Zyklen (DFS-Faerbung), leer = ok.
func pruefeGraph(zs []planAufgabe) []string {
	var probleme []string
	ids := map[string]bool{}
	deps := map[string][]string{}
	for _, z := range zs {
		ids[z.ID] = true
		deps[z.ID] = z.Deps
	}
	for _, z := range zs {
		for _, d := range z.Deps {
			if !ids[d] {
				probleme = append(probleme, fmt.Sprintf("%s: Abhaengigkeit '%s' existiert nicht", z.ID, d))
			}
		}
	}

	farbe := map[string]uint8{} // 0 weiss, 1 grau, 2 schwarz
	var besuch func(k string, pfad []string)
	besuch = func(k string, pfad []string) {
		farbe[k] = 1
		for _, d := range deps[k] {
			if !ids[d] {
				continue // schon oben gemeldet
			}
			switch farbe[d] {
			case 1:
				probleme = append(probleme, "Zyklus: "+strings.Join(append(slices.Clone(pfad), k, d), " -> "))
			case 0:
				besuch(d, append(slices.Clone(pfad), k))
			}
		}
		farbe[k] = 2
	}
	for _, i := range slices.Sorted(maps.Keys(ids)) {
		if farbe[i] == 0 {
			besuch(i, nil)
		}
	}
	return probleme
}

// planWarnungen: nicht blockierende Hinweise auf mehrdeutige Abhaengigkeiten.
func planWarnungen(zs []planAufgabe) []string {
	ids := map[string]bool{}
	for _, z := range zs {
		ids[z.ID] = true
	}
	hatKinder := map[string]bool{}
	for i := range ids {
		for j := range ids {
			if strings.HasPrefix(j, i+".") {
				hatKinder[i] = true
				break
			}
		}
	}
	var out []string
	for _, z := range zs {
		for _, d := range z.Deps {
			if hatKinder[d] && !strings.HasPrefix(z.ID, d+".") {
				out = append(out, fmt.Sprintf("%s haengt an '%s', das Unteraufgaben hat - gemeint ist die Task '%s', nicht der ganze Teilbaum %s.x", z.ID, d, d, d))
			}
		}
	}
	return out
}

// statusTabelle: mit Status-Spalte gilt nur die Datei, sonst planStatus.
// Bei doppelten IDs gewinnt die letzte Zeile, wie im Graph.
func statusTabelle(d planDatei) map[string]string {
	if !d.HatStatus {
		return planStatus
	}
	st := map[string]string{}
	for _, a := range d.Zeilen {
		if a.Status != "" && a.Status != "OFFEN" {
			st[a.ID] = a.Status
		} else {
			delete(st, a.ID)
		}
	}
	return st
}

func statusVon(st map[string]string, id string) string {
	if s, ok := st[id]; ok {
		return s
	}
	return "OFFEN"
}

// readyUndBlockiert: das Gate je offener Aufgabe, Reihenfolge = CSV.
func readyUndBlockiert(zs []planAufgabe, st map[string]string) (ready []planAufgabe, blockiert []planBlockade) {
	for _, z := range zs {
		if statusVon(st, z.ID) != "OFFEN" {
			continue
		}
		var fehlend []string
		for _, d := range z.Deps {
			if statusVon(st, d) != "FERTIG" {
				fehlend = append(fehlend, d)
			}
		}
		if len(fehlend) > 0 {
			blockiert = append(blockiert, planBlockade{A: z, Fehlend: fehlend})
			continue
		}
		ready = append(ready, z)
	}
	return ready, blockiert
}

// pyErr liefert die Fehlermeldung ohne die angehaengte Go-Sentinel-Kette,
// so wie Python str(e) nur den Text zeigt.
func pyErr(err error) string {
	return strings.TrimSuffix(err.Error(), ": "+ErrValue.Error())
}

// planMain ist main() aus plan.py; Exit 0 ok, 1 Lesefehler, 2 Graph
// kaputt, 3 Zeitplan verletzt die Claude-Grenze (Plan wird trotzdem
// ausgegeben, damit man sieht, was zu teilen ist).
func planMain(pfad string, w io.Writer) int {
	pfad = filepath.Clean(pfad)
	fmt.Fprintf(w, "[1/4] Lese %s\n", pfad)
	text, err := liesText(pfad)
	var datei planDatei
	if err == nil {
		if strings.HasSuffix(pfad, ".jsonl") {
			datei, err = ladeDashboard(text)
		} else {
			datei, err = parseZeilen(text)
		}
	}
	zs := datei.Zeilen
	if err != nil {
		fmt.Fprintf(w, "      FEHLER: %s\n", pyErr(err))
		return 1
	}
	fmt.Fprintf(w, "      %d Aufgaben geladen\n", len(zs))

	fmt.Fprintln(w, "[2/4] Pruefe Abhaengigkeits-Graph")
	if probleme := pruefeGraph(zs); len(probleme) > 0 {
		for _, p := range probleme {
			fmt.Fprintf(w, "      FEHLER: %s\n", p)
		}
		fmt.Fprintln(w, "      -> Graph kaputt, keine Berechnung.")
		return 2
	}
	fmt.Fprintln(w, "      ok: alle Abhaengigkeiten aufloesbar, keine Zyklen")
	for _, h := range planWarnungen(zs) {
		fmt.Fprintf(w, "      HINWEIS: %s\n", h)
	}

	st := statusTabelle(datei)
	herkunft := "fest verdrahtet"
	if datei.HatStatus {
		herkunft = "aus der Datei"
	}
	fmt.Fprintf(w, "[3/4] Status (%s, alle nicht genannten = OFFEN):\n", herkunft)
	for _, id := range slices.Sorted(maps.Keys(st)) {
		fmt.Fprintf(w, "      %s = %s\n", id, st[id])
	}

	fmt.Fprintln(w, "[4/4] Berechne zulaessige naechste Aufgaben")
	ready, blockiert := readyUndBlockiert(zs, st)
	fmt.Fprintf(w, "\nZULAESSIG (%d):\n", len(ready))
	for _, z := range ready {
		fmt.Fprintf(w, "  %-6s  %s\n", z.ID, z.Aufgabe)
	}
	fmt.Fprintf(w, "\nBLOCKIERT (%d):\n", len(blockiert))
	for _, b := range blockiert {
		fmt.Fprintf(w, "  %-6s  <- wartet auf %s\n", b.A.ID, strings.Join(b.Fehlend, ", "))
	}
	if !datei.HatDauer {
		return 0
	}
	return zeitplan(zs, st, w)
}

// planZeit ist das Ergebnis der Vorwaerts-/Rueckwaertsrechnung je Aufgabe,
// alles in Sekunden ab jetzt.
type planZeit struct {
	A                      planAufgabe
	Dauer, Start, Ende, LS int64
}

func (z planZeit) Puffer() int64 { return z.LS - z.Start }

// zeitplanRechnen: kritischer Pfad ueber den (geprueften, azyklischen)
// Graph. FERTIG zaehlt 0. Topologische Reihenfolge nach Kahn, Start in
// Datei-Reihenfolge, damit das Ergebnis deterministisch ist. O(V+E).
func zeitplanRechnen(zs []planAufgabe, st map[string]string) (reihe []planZeit, ende int64, pfad []string) {
	letzte := map[string]planAufgabe{} // doppelte IDs: letzte Zeile gewinnt
	var ordnung []string
	for _, a := range zs {
		if _, ok := letzte[a.ID]; !ok {
			ordnung = append(ordnung, a.ID)
		}
		letzte[a.ID] = a
	}
	nach := map[string][]string{}
	grad := map[string]int{}
	for _, id := range ordnung {
		for _, d := range letzte[id].Deps {
			nach[d] = append(nach[d], id)
			grad[id]++
		}
	}
	var topo, schlange []string
	for _, id := range ordnung {
		if grad[id] == 0 {
			schlange = append(schlange, id)
		}
	}
	for len(schlange) > 0 {
		id := schlange[0]
		schlange = schlange[1:]
		topo = append(topo, id)
		for _, n := range nach[id] {
			if grad[n]--; grad[n] == 0 {
				schlange = append(schlange, n)
			}
		}
	}

	z := map[string]*planZeit{}
	for _, id := range topo {
		a := letzte[id]
		pz := &planZeit{A: a}
		if statusVon(st, id) != "FERTIG" {
			pz.Dauer = a.dauerSekunden()
		}
		for _, d := range a.Deps {
			pz.Start = max(pz.Start, z[d].Ende)
		}
		pz.Ende = pz.Start + pz.Dauer
		ende = max(ende, pz.Ende)
		z[id] = pz
	}
	spaetEnde := map[string]int64{}
	for _, id := range slices.Backward(topo) {
		lf := ende
		for _, n := range nach[id] {
			lf = min(lf, z[n].LS)
		}
		spaetEnde[id] = lf
		z[id].LS = lf - z[id].Dauer
	}

	// Kritischer Pfad rueckwaerts: vom spaetesten kritischen Ende ueber
	// Vorgaenger ohne Puffer, deren Ende genau den Start traegt.
	var cur *planZeit
	for _, id := range topo {
		if p := z[id]; p.Puffer() == 0 && p.Ende == ende && p.Dauer > 0 {
			cur = p
		}
	}
	for cur != nil {
		pfad = append(pfad, cur.A.ID)
		var vor *planZeit
		for _, d := range cur.A.Deps {
			if p := z[d]; p.Puffer() == 0 && p.Ende == cur.Start && p.Dauer > 0 {
				vor = p
				break
			}
		}
		cur = vor
	}
	slices.Reverse(pfad)

	for _, a := range zs {
		if statusVon(st, a.ID) != "FERTIG" && z[a.ID] != nil {
			reihe = append(reihe, *z[a.ID])
		}
	}
	return reihe, ende, pfad
}

func hmm(sek int64) string { return fmt.Sprintf("%d:%02d", sek/3600, sek%3600/60) }

// zeitplan gibt Startzeiten, Puffer, kritischen Pfad, Aufwand und Wochen
// aus und prueft die Claude-Grenze; Exit 3 bei Verletzung.
func zeitplan(zs []planAufgabe, st map[string]string, w io.Writer) int {
	reihe, ende, pfad := zeitplanRechnen(zs, st)
	fmt.Fprintf(w, "\nZEITPLAN (h:mm ab jetzt; Sitzung = %d min, claude-Sitzung = %d min; FERTIG zaehlt 0):\n",
		sitzungMinuten, claudeSitzungMinuten)
	fmt.Fprintf(w, "  %-6s  %-11s  %6s  %6s  %6s  %6s\n", "ID", "Werkzeug", "Dauer", "Start", "Ende", "Puffer")
	var aufwand int64
	var verstoss []string
	for _, z := range reihe {
		krit := ""
		if z.Puffer() == 0 && z.Dauer > 0 {
			krit = "  *"
		}
		wz := z.A.Werkzeug
		if wz == "" {
			wz = "-"
		}
		fmt.Fprintf(w, "  %-6s  %-11s  %6s  %6s  %6s  %6s%s\n",
			z.A.ID, wz, hmm(z.Dauer), hmm(z.Start), hmm(z.Ende), hmm(z.Puffer()), krit)
		aufwand += z.Dauer
		if z.A.Werkzeug == "claude" && z.A.Dauer > claudeMaxSitzungen {
			verstoss = append(verstoss, fmt.Sprintf("%s: claude-Aufgabe mit %s Sitzungen (%s) > %d Sitzung (%d min) - teilen",
				z.A.ID, strconv.FormatFloat(z.A.Dauer, 'f', -1, 64), hmm(z.Dauer), claudeMaxSitzungen, claudeSitzungMinuten))
		}
	}
	fmt.Fprintf(w, "\nKRITISCHER PFAD (%s, Untergrenze bei voller Parallelitaet): %s\n", hmm(ende), strings.Join(pfad, " -> "))
	fmt.Fprintf(w, "GESAMTAUFWAND: %s in %d Aufgaben\n", hmm(aufwand), len(reihe))
	h := float64(aufwand) / 3600
	fmt.Fprintf(w, "WOCHEN bei %d-%d h/Woche (seriell gerechnet): %.1f - %.1f\n",
		wocheMinStunden, wocheMaxStunden, h/wocheMaxStunden, h/wocheMinStunden)
	if len(verstoss) == 0 {
		return 0
	}
	fmt.Fprintln(w)
	for _, v := range verstoss {
		fmt.Fprintf(w, "FEHLER: %s\n", v)
	}
	return 3
}

// --- Detektoren: unabhaengige Pruefer der Engine-Invarianten ---------

// monoton (I): jeder Fakt von vorher steht auch in nachher.
func monoton(vorher, nachher string) bool {
	n := fakten(nachher)
	for f := range fakten(vorher) {
		if _, ok := n[f]; !ok {
			return false
		}
	}
	return true
}

// zaehle: wie oft steht fakt als getrimmte Zeile in text.
func zaehle(text, fakt string) int {
	n := 0
	for _, z := range pySplitlines(text) {
		if pyStrip(z) == fakt {
			n++
		}
	}
	return n
}

// --- Harness: Python-repr fuer Paritaet mit ref/*.json ---------------

type tuple []any

// pyset bildet ein Python-set kleiner ints nach; Python zeigt es sortiert.
type pyset []int

func pyRepr(v any) string {
	switch x := v.(type) {
	case nil:
		return "None"
	case bool:
		if x {
			return "True"
		}
		return "False"
	case int:
		return strconv.Itoa(x)
	case int64:
		return strconv.FormatInt(x, 10)
	case uint8:
		return strconv.Itoa(int(x))
	case float64:
		return pyFloat(x)
	case time.Duration:
		return pyFloat(x.Seconds())
	case string:
		return pyStr(x)
	case Status:
		return pyStr(x.String())
	case []string:
		parts := make([]string, len(x))
		for i, e := range x {
			parts[i] = pyStr(e)
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case tuple:
		parts := make([]string, len(x))
		for i, e := range x {
			parts[i] = pyRepr(e)
		}
		if len(x) == 1 {
			return "(" + parts[0] + ",)"
		}
		return "(" + strings.Join(parts, ", ") + ")"
	case pyset:
		if len(x) == 0 {
			return "set()"
		}
		s := slices.Clone(x)
		slices.Sort(s)
		s = slices.Compact(s)
		parts := make([]string, len(s))
		for i, e := range s {
			parts[i] = strconv.Itoa(e)
		}
		return "{" + strings.Join(parts, ", ") + "}"
	}
	return fmt.Sprintf("%v", v)
}

// pyFloat bildet Pythons repr(float) nach: kuerzeste Ziffernfolge,
// wissenschaftlich bei Exponent < -4 oder >= 16, sonst immer mit Punkt.
func pyFloat(f float64) string {
	switch {
	case math.IsNaN(f):
		return "nan"
	case math.IsInf(f, 1):
		return "inf"
	case math.IsInf(f, -1):
		return "-inf"
	}
	e := strconv.FormatFloat(f, 'e', -1, 64)
	exp, _ := strconv.Atoi(e[strings.IndexByte(e, 'e')+1:]) // 'e'-Format liefert immer einen Exponenten
	if exp < -4 || exp >= 16 {
		return e
	}
	s := strconv.FormatFloat(f, 'f', -1, 64)
	if !strings.ContainsRune(s, '.') {
		s += ".0"
	}
	return s
}

// pyStr bildet Pythons repr(str) nach: einfache Quotes, ausser der String
// enthaelt ' aber kein ".
func pyStr(s string) string {
	q := '\''
	if strings.ContainsRune(s, '\'') && !strings.ContainsRune(s, '"') {
		q = '"'
	}
	var b strings.Builder
	b.WriteRune(q)
	for _, r := range s {
		switch {
		case r == '\\' || r == q:
			b.WriteByte('\\')
			b.WriteRune(r)
		case r == '\n':
			b.WriteString(`\n`)
		case r == '\r':
			b.WriteString(`\r`)
		case r == '\t':
			b.WriteString(`\t`)
		case unicode.IsPrint(r):
			b.WriteRune(r)
		case r < 0x100:
			fmt.Fprintf(&b, `\x%02x`, r)
		case r < 0x10000:
			fmt.Fprintf(&b, `\u%04x`, r)
		default:
			fmt.Fprintf(&b, `\U%08x`, r)
		}
	}
	b.WriteRune(q)
	return b.String()
}

type check struct {
	Name     string `json:"name"`
	Erwartet string `json:"erwartet"`
	Gemessen string `json:"gemessen"`
	Pass     bool   `json:"pass"`
}

type report struct {
	Saeule     string  `json:"saeule"`
	Invariante string  `json:"invariante"`
	GeprueftAm string  `json:"geprueft_am"`
	CodeHash   string  `json:"code_hash,omitempty"`
	Checks     []check `json:"checks"`
	Ergebnis   string  `json:"ergebnis"`
}

func (r *report) expect(name string, want, got any) {
	w, g := pyRepr(want), pyRepr(got)
	r.Checks = append(r.Checks, check{Name: name, Erwartet: w, Gemessen: g, Pass: w == g})
}

func (r *report) finish() bool {
	r.Ergebnis = "BESTANDEN"
	for _, c := range r.Checks {
		if !c.Pass {
			r.Ergebnis = "NICHT BESTANDEN"
			return false
		}
	}
	return true
}

// checkS1: Checks 3-6 aus ref/S1-zustand.json brauchen trigger/Step (Schritt 4).
func checkS1() report {
	r := report{
		Saeule:     "ZUSTAND",
		Invariante: "SharedState-Felder haben immer die erwarteten Typen/Werte; last_pulse waechst nur bei WAKE",
	}

	s := newState()
	r.expect("Start: status SLEEP, tick 0, data None",
		tuple{"SLEEP", 0, nil}, tuple{s.Status, s.Tick, s.data()})
	r.expect("frischer Zustand ist konsistent", true, s.konsistent())

	// Rekonstruierter Aufbau: interval 0.5s, Uhr steht bei 0, dann 1.0s.
	var now time.Duration
	l := newLoop(500*time.Millisecond, func() time.Duration { return now })
	_, err := l.Step("VALID")
	r.expect("nach EXECUTE: tick 1, status UPDATED, data gesetzt",
		tuple{1, "UPDATED", "VALID"}, tuple{l.State.Tick, l.State.Status, l.State.data()})
	_, err2 := l.Step(nil)
	r.expect("SLEEP aendert last_pulse nicht", 0.0, l.State.LastPulse)
	r.expect("SLEEP erhoeht tick nicht", 1, l.State.Tick)
	now = time.Second
	_, err3 := l.Step(nil)
	r.expect("WAKE nach Zeitablauf setzt last_pulse neu", true, l.State.LastPulse == now)
	r.expect("Steps ohne Fehler", nil, errors.Join(err, err2, err3))

	s.Tick = -1
	r.expect("inkonsistenter tick -> konsistent() False", false, s.konsistent())

	// Go-spezifisch: die Bitmaske selbst.
	s = newState()
	s.Status = Wake | Updated
	r.expect("zwei Status-Bits -> konsistent() False", false, s.konsistent())
	s.Status = 1 << 7
	r.expect("Bit ausserhalb validMask -> konsistent() False", false, s.konsistent())
	s.Status = 0
	r.expect("kein Status-Bit -> konsistent() False", false, s.konsistent())

	return r
}

func checkS2() report {
	r := report{
		Saeule:     "TRANSFORMATION",
		Invariante: "AlphaGenerator: rohe Eingabe -> Payload, nie None, deterministisch",
	}

	r.expect("None -> 'PING' (Heartbeat)", "PING", transform(nil))
	r.expect("'X' -> 'X' (Durchreichung)", "X", transform("X"))
	r.expect("0 -> 0 (nicht None -> durchgereicht)", 0, transform(0))

	nieNil := true
	for _, raw := range []any{nil, "X", 0, "", false, []any{}, map[string]any{}} {
		nieNil = nieNil && transform(raw) != nil
	}
	r.expect("nie None", true, nieNil)

	var det any = "<abweichend>"
	if a, b := transform("q"), transform("q"); a == b {
		det = a
	}
	r.expect("deterministisch", "q", det)

	return r
}

func checkS3() report {
	r := report{
		Saeule:     "INFORMATION",
		Invariante: "BravoValidator erzeugt GENAU ein Bit 0/1; 1 nur bei gueltigem Schema (str, nicht-leer, nicht Blockliste, <=MAX_LEN)",
	}
	bit := func(p any) uint8 { b, _ := inform(p); return b }

	r.expect("gueltiger String -> 1", 1, bit("gueltig"))
	r.expect("'INVALID' -> 0", 0, bit("INVALID"))
	r.expect("'CORRUPT' -> 0", 0, bit("CORRUPT"))
	r.expect("'' -> 0", 0, bit(""))
	r.expect("'   ' -> 0", 0, bit("   "))
	r.expect("dict -> 0 (falscher Typ)", 0, bit(map[string]any{"a": 1}))
	r.expect("list -> 0", 0, bit([]any{"a"}))
	r.expect("int -> 0", 0, bit(5))
	r.expect("None -> 0", 0, bit(nil))
	r.expect("uebermassig lang -> 0", 0, bit(strings.Repeat("x", maxLen+1)))
	r.expect("'BANANA' -> 1 (Schema erlaubt beliebigen Inhalt, nur Form zaehlt)", 1, bit("BANANA"))

	inputs := []any{
		"gueltig", "INVALID", "CORRUPT", "", "   ", "BANANA", nil, 5, 1.5, true,
		map[string]any{}, []any{}, json.Number("7"), strings.Repeat("x", maxLen+1),
	}
	var out pyset
	for _, p := range inputs {
		out = append(out, int(bit(p)))
	}
	r.expect("Ausgabe immer exakt 0 oder 1 (int)", pyset{0, 1}, out)

	var det any = "<abweichend>"
	if a, b := bit("gueltig"), bit("gueltig"); a == b {
		det = a
	}
	r.expect("deterministisch", 1, det)

	// Go-spezifisch: die any-Grenze dicht halten.
	r.expect("float64 -> 0 (JSON-Zahl)", 0, bit(0.0))
	r.expect("bool -> 0", 0, bit(true))
	r.expect("json.Number -> 0 (eigener Typ, kein string)", 0, bit(json.Number("1")))
	// Go-spezifisch: Python-Whitespace und Codepoint-Laenge.
	r.expect("'\\x1f' -> 0 (Python-Whitespace)", 0, bit("\x1f"))
	r.expect("4096 x 'ä' -> 1 (Codepoints, nicht Bytes)", 1, bit(strings.Repeat("ä", maxLen)))
	r.expect("4097 x 'ä' -> 0", 0, bit(strings.Repeat("ä", maxLen+1)))
	// Go-spezifisch: Grund-Maske und gateBit.
	_, g := inform("  INVALID ")
	r.expect("Grund('  INVALID ') == GrundBlock", int(GrundBlock), int(g))
	gateOK := true
	for m := range grundAlle + 1 {
		gateOK = gateOK && (gateBit(m) == 1) == (m == 0)
	}
	r.expect("gateBit(m) == 1 genau fuer m == 0 (alle Masken 0..grundAlle)", true, gateOK)
	// Go-spezifisch: pyIsSpace gegen Pythons str.isspace, alle Codepoints.
	abw, err := pyIsSpaceParitaet()
	if err != nil {
		abw = err.Error()
	}
	r.expect("pyIsSpace == Python str.isspace (U+0000..U+10FFFF)", "", abw)
	// Go-spezifisch: Goroutine-Stufen == serielle Schleife.
	serial := make([]paket, len(inputs))
	for i, raw := range inputs {
		p := transform(raw)
		b, gr := inform(p)
		serial[i] = paket{Payload: p, Bit: b, Grund: gr}
	}
	r.expect("tiPipeline == seriell (Reihenfolge, Bit, Grund)", true, sameTI(serial, tiPipeline(inputs)))
	r.expect("tiParallel == seriell (Reihenfolge, Bit, Grund)", true, sameTI(serial, tiParallel(inputs)))

	return r
}

// pyIsSpaceParitaet vergleicht pyIsSpace mit ref/py-isspace.json und
// liefert den ersten abweichenden Codepoint, sonst "".
func pyIsSpaceParitaet() (string, error) {
	raw, err := os.ReadFile("ref/py-isspace.json")
	if err != nil {
		return "", err
	}
	var ref struct {
		Codepoints []rune `json:"codepoints"`
	}
	if err := json.Unmarshal(raw, &ref); err != nil {
		return "", fmt.Errorf("ref/py-isspace.json: %w", err)
	}
	want := make(map[rune]bool, len(ref.Codepoints))
	for _, c := range ref.Codepoints {
		want[c] = true
	}
	for r := range rune(unicode.MaxRune + 1) {
		if pyIsSpace(r) != want[r] {
			return fmt.Sprintf("U+%04X", r), nil
		}
	}
	return "", nil
}

func checkS5() report {
	r := report{
		Saeule:     "INTERFERENZ",
		Invariante: "Chrono-Trigger SLEEP/WAKE; Bit=0 -> validierter RESET; Pre-Wake-Check; INVALID/Zustandsbruch/Wiederholung",
	}
	// Rekonstruierter Aufbau: interval 0.5s, Uhr pro Check frisch bei 0.
	var now time.Duration
	neu := func() *Loop { now = 0; return newLoop(500*time.Millisecond, func() time.Duration { return now }) }
	var errs []error
	step := func(l *Loop, raw any) string {
		res, err := l.Step(raw)
		errs = append(errs, err)
		return res.String()
	}

	l := neu()
	r.expect("kein Input + Zeit nicht abgelaufen -> SLEEP", "SLEEP", step(l, nil))
	now = time.Second
	r.expect("Zeit abgelaufen -> WAKE (kein SLEEP)", true, step(l, nil) != "SLEEP")
	r.expect("Input vorhanden vor Intervall -> WAKE", true, step(neu(), "x") != "SLEEP")

	l = neu()
	r.expect("INVALID -> RESET (BIT=0)", true, strings.Contains(step(l, "INVALID"), "RESET (BIT=0)"))
	r.expect("INVALID -> data auf None (Charlie-RESET)", nil, l.State.data())
	r.expect("INVALID -> status CLEAN", "CLEAN", l.State.Status)

	s := State{Data: "muell", HasData: true, Tick: 7, Status: Updated}
	alt, err := deltaReset(&s, nil)
	errs = append(errs, err)
	r.expect("Charlie protokolliert Alt-Wert", "muell", alt.Data)
	r.expect("Charlie: data None, status CLEAN, tick erhalten (war gueltig)",
		tuple{nil, "CLEAN", 7}, tuple{s.data(), s.Status, s.Tick})

	// Rekonstruiert: Zustandsbruch per negativem Tick.
	l = neu()
	l.State.Tick = -1
	res := step(l, "neue daten")
	r.expect("Zustandsbruch -> PRE-WAKE RESET", true, strings.Contains(res, "PRE-WAKE RESET"))
	r.expect("Zustandsbruch -> kein EXECUTE (data nicht 'neue daten')", true, l.State.data() != "neue daten")
	r.expect("Zustandsbruch -> Zustand nach RESET wieder konsistent", true, l.State.konsistent())

	a, b := neu(), neu()
	resA, resB := step(a, "wiederhol"), step(b, "wiederhol")
	var wieder any = "<abweichend>"
	if resA == resB {
		wieder = resA
	}
	r.expect("Wiederholung: identisches Ergebnis bei identischem Start",
		"TICK 1: EXECUTE (BIT=1) -> State: 'wiederhol'", wieder)
	r.expect("Wiederholung: gleicher Zustand", tuple{"wiederhol", "UPDATED"}, tuple{a.State.data(), a.State.Status})
	step(a, "wiederhol")
	r.expect("zweiter EXECUTE mit selbem Payload: data unveraendert (idempotent auf data)", "wiederhol", a.State.data())

	// Go-spezifisch: Quirks explizit.
	l = neu()
	step(l, "INVALID")
	step(l, nil)
	r.expect("SLEEP ueberschreibt CLEAN (Quirk 2)", "SLEEP", l.State.Status)
	l = neu()
	now = 2 * time.Second
	l.State.Tick = -1
	step(l, nil)
	r.expect("Pre-Wake-Reset: tick 0, LastPulse bleibt neu gesetzt (Quirk 3)",
		tuple{0, 2.0}, tuple{l.State.Tick, l.State.LastPulse})
	l = neu()
	step(l, "INVALID")
	r.expect("RESET-Step erhoeht tick (Quirk 5)", 1, l.State.Tick)
	r.expect("alle Steps ohne Fehler", nil, errors.Join(errs...))

	return r
}

// checkLauf spielt ref/00-lauf.json als JSONL durch laufStream in der
// gegebenen Phase und vergleicht je Schritt t, status, ergebnis (Variante A).
// tick/bit sind nur Diagnose.
func checkLauf(phase string) report {
	r := report{Saeule: "LAUF-" + strings.ToUpper(phase)}
	raw, err := os.ReadFile("ref/00-lauf.json")
	if err != nil {
		r.expect("ref/00-lauf.json lesbar", nil, err.Error())
		return r
	}
	var ref struct {
		Beschreibung string `json:"beschreibung"`
		Schritte     []struct {
			T        float64 `json:"t"`
			Input    any     `json:"input"`
			Status   string  `json:"status"`
			Ergebnis string  `json:"ergebnis"`
		} `json:"schritte"`
	}
	if err := json.Unmarshal(raw, &ref); err != nil {
		r.expect("ref/00-lauf.json parsebar", nil, err.Error())
		return r
	}
	r.Invariante = ref.Beschreibung

	var in, out bytes.Buffer
	enc := json.NewEncoder(&in)
	for _, st := range ref.Schritte {
		if err := enc.Encode(map[string]any{"t": st.T, "input": st.Input}); err != nil {
			r.expect("JSONL-Eingabe erzeugt", nil, err.Error())
			return r
		}
	}
	// interval steht nur in beschreibung: 0.5s.
	if err := laufStream(&in, &out, io.Discard, 500*time.Millisecond, phase); err != nil {
		r.expect("laufStream ohne Fehler", nil, err.Error())
		return r
	}

	dec := json.NewDecoder(&out)
	for i, st := range ref.Schritte {
		var a ausgabe
		got := any(nil)
		if err := dec.Decode(&a); err != nil {
			got = err.Error()
		} else {
			got = tuple{a.T, a.Status, a.Ergebnis}
		}
		r.expect(fmt.Sprintf("[Step %d] t=%.1f", i+1, st.T), tuple{st.T, st.Status, st.Ergebnis}, got)
	}
	r.expect("keine ueberzaehligen Ausgabezeilen", false, dec.More())
	return r
}

// --- Stress ----------------------------------------------------------

var stressProcs = []int{1, 2, 3, 4, 8}

// stressPool sind die Rohwerte, aus denen Stress-Laeufe ziehen; nil kommt
// mehrfach vor, damit SLEEP-Steps haeufig sind.
var stressPool = []any{
	nil, nil, nil, nil, "VALID_DATA", "INVALID", "CORRUPT", "", "   ", "  x  ",
	"it's", "ä", 0.0, 1.5, true, map[string]any{"a": 1.0}, []any{"x"},
	strings.Repeat("x", maxLen+1), "\x1fINVALID\x1f",
}

// stressEingabe erzeugt aus seed deterministisch einen JSONL-Lauf: dt in
// {0.0..0.7}s, gelegentlich ein Ruecksprung, und die rohen Eingaben.
func stressEingabe(seed uint64, steps int) ([]byte, []any, error) {
	rng := rand.New(rand.NewPCG(seed, 0x5a7))
	var buf bytes.Buffer
	enc := json.NewEncoder(&buf)
	raws := make([]any, steps)
	t := 0.0
	for i := range steps {
		t += float64(rng.IntN(8)) / 10
		if rng.IntN(50) == 0 {
			t -= 0.4
		}
		raws[i] = stressPool[rng.IntN(len(stressPool))]
		if err := enc.Encode(map[string]any{"t": t, "input": raws[i]}); err != nil {
			return nil, nil, err
		}
	}
	return buf.Bytes(), raws, nil
}

// stress laeuft n Seeds je GOMAXPROCS-Wert und vergleicht positionsgleich:
// Phase B gegen Phase A (JSONL byte-genau) und tiParallel gegen tiSeriell.
// GOMAXPROCS ist prozessweit; es wird je Wert gesetzt und am Ende
// zurueckgestellt. Liefert je Pruefung die erste Abweichung oder "".
func stress(n, steps int) (phaseAB, parallel string, err error) {
	defer runtime.GOMAXPROCS(runtime.GOMAXPROCS(0))
	for _, procs := range stressProcs {
		runtime.GOMAXPROCS(procs)
		for seed := range uint64(n) {
			jsonl, raws, err := stressEingabe(seed, steps)
			if err != nil {
				return "", "", err
			}
			var a, b bytes.Buffer
			if err := laufStream(bytes.NewReader(jsonl), &a, io.Discard, 500*time.Millisecond, "a"); err != nil {
				return "", "", err
			}
			if err := laufStream(bytes.NewReader(jsonl), &b, io.Discard, 500*time.Millisecond, "b"); err != nil {
				return "", "", err
			}
			where := fmt.Sprintf("GOMAXPROCS=%d seed=%d", procs, seed)
			if phaseAB == "" && !bytes.Equal(a.Bytes(), b.Bytes()) {
				phaseAB = where
			}
			serial := make([]paket, len(raws))
			for i, raw := range raws {
				serial[i] = tiSeriell(raw)
			}
			if parallel == "" && !sameTI(serial, tiParallel(raws)) {
				parallel = where
			}
		}
	}
	return phaseAB, parallel, nil
}

// warteGoroutines wartet kurz, bis beendete Goroutines abgebaut sind.
func warteGoroutines(soll int) int {
	n := runtime.NumGoroutine()
	for i := 0; i < 100 && n > soll; i++ {
		time.Sleep(time.Millisecond)
		n = runtime.NumGoroutine()
	}
	return n
}

func checkStress(n int) report {
	r := report{
		Saeule:     "STRESS",
		Invariante: "Phase B == Phase A positionsgleich; tiParallel == tiSeriell; SLEEP beruehrt T/I nicht; keine Goroutine-Leaks",
	}
	vorher := runtime.NumGoroutine()

	abw, par, err := stress(n, 64)
	if err != nil {
		abw, par = err.Error(), err.Error()
	}
	label := fmt.Sprintf("%d Seeds x GOMAXPROCS %v x 64 Steps", n, stressProcs)
	r.expect("Phase B == Phase A, JSONL byte-genau ("+label+")", "", abw)
	r.expect("tiParallel == tiSeriell positionsgleich ("+label+")", "", par)

	// ti wird genau fuer RESET/EXECUTE-Steps gerufen, nie fuer SLEEP/PRE-WAKE.
	_, raws, err := stressEingabe(1, 256)
	r.expect("stressEingabe ohne Fehler", nil, err)
	var now, t time.Duration
	l := newLoop(500*time.Millisecond, func() time.Duration { return now })
	calls := 0
	l.ti = func(raw any) paket { calls++; return tiSeriell(raw) }
	gate := 0
	for _, raw := range raws {
		t += 300 * time.Millisecond
		now = t
		res, _ := l.Step(raw)
		if res.Kind >= KindReset {
			gate++
		}
	}
	r.expect("ti-Aufrufe == RESET/EXECUTE-Steps (SLEEP beruehrt T/I nicht)", gate, calls)

	// Nicht-monotone Uhr: Warnung, Ausgabe wie Python.
	var out, warn bytes.Buffer
	in := strings.NewReader(`{"t":1.0,"input":"a"}` + "\n" + `{"t":0.4}` + "\n")
	err = laufStream(in, &out, &warn, 500*time.Millisecond, "b")
	r.expect("t rueckwaerts: Warnung auf warn, Step 2 SLEEP, kein Fehler",
		tuple{true, true, nil},
		tuple{strings.Contains(warn.String(), "schritt 2: t laeuft rueckwaerts"), strings.HasSuffix(out.String(), `"ergebnis":"SLEEP"}`+"\n"), err})

	r.expect("keine Goroutine-Leaks", vorher, warteGoroutines(vorher))
	return r
}

// --- Checks: Kanon -----------------------------------------------------

func checkKanon() report {
	r := report{Saeule: "KANON", Invariante: "Main.go folgt kanon.json: Positionen, Woerter je Layer, Adresse, Gate-Zuordnung"}
	raw, err := os.ReadFile("kanon.json")
	if err != nil {
		r.expect("kanon.json lesbar", nil, err.Error())
		return r
	}
	var k struct {
		Layer map[string]struct {
			Woerter []*string `json:"woerter"`
		} `json:"layer"`
		Gate map[string]string `json:"gate"`
	}
	if err := json.Unmarshal(raw, &k); err != nil {
		r.expect("kanon.json parsebar", nil, err.Error())
		return r
	}
	woerter := func(layer string) []string {
		var out []string
		for _, w := range k.Layer[layer].Woerter {
			if w == nil {
				out = append(out, "<offen>")
				continue
			}
			out = append(out, *w)
		}
		return out
	}
	r.expect("Objekt-Woerter == kanon.layer.objekt", woerter("objekt"), objektWoerter[:])
	r.expect("Operator-Woerter == kanon.layer.operator", woerter("operator"), operatorWoerter[:])
	var t struct {
		Layer map[string]struct {
			Taetigkeiten []string `json:"taetigkeiten"`
		} `json:"layer"`
	}
	_ = json.Unmarshal(raw, &t) // Parsefehler wuerde oben schon gemeldet
	r.expect("Operator-Taetigkeiten == kanon.layer.operator.taetigkeiten", t.Layer["operator"].Taetigkeiten, operatorTaetigkeiten[:])
	r.expect("Router hat 4 Positionen", 4, len(k.Layer["router"].Woerter))

	rund := true
	for a := range Adresse(64) {
		rund = rund && Adr(a.Objekt(), a.Operator(), a.Zoom()) == a
	}
	r.expect("Adresse: alle 64 Kombinationen eindeutig und umkehrbar", true, rund)
	r.expect("Adresse 'auf Zustand, mit Bravo, Zoom 1' == 0x04", "0x04", fmt.Sprintf("%#02x", uint8(Adr(Zustand, Bravo, 0))))
	r.expect("Adresse.String", "Zustand/Bravo/Zoom1", Adr(Zustand, Bravo, 0).String())

	pos := struct {
		Positionen []string `json:"positionen"`
	}{}
	_ = json.Unmarshal(raw, &pos) // Parsefehler wuerde oben schon gemeldet
	r.expect("Positions-Bedeutungen == kanon.positionen", pos.Positionen, posBedeutung[:])

	// Dispatcher: jeder Begriff findet seine Stelle, alles andere ist unbekannt.
	alle := true
	for l := range layerAnzahl {
		for p, w := range begriffStelle[l] {
			if w == "" {
				continue
			}
			st, ok := Ordne(w)
			alle = alle && ok && st.Layer == l && st.Pos == uint8(p)
		}
	}
	r.expect("Ordne: jeder Kanon-Begriff an seiner festen Stelle", true, alle)
	sb, okB := Ordne("  bravo ")
	r.expect("Ordne(' bravo ') -> operator, Position 2", tuple{true, "operator", 2}, tuple{okB, layerNamen[sb.Layer], int(sb.Pos) + 1})
	st, _ := Ordne("Transformation")
	r.expect("Bravo und Transformation: gleiche Position, anderer Layer", tuple{true, true},
		tuple{sb.Pos == st.Pos, sb.Layer != st.Layer})
	r.expect("Bravo.GleichePosition", []string{"Transformation"}, sb.GleichePosition())
	sv, okV := Ordne("Validieren")
	r.expect("Ordne('Validieren') -> operator, Position 3 (= Charlie)", tuple{true, "operator", 3, "Charlie"},
		tuple{okV, layerNamen[sv.Layer], int(sv.Pos) + 1, operatorWoerter[sv.Pos]})
	_, okU := Ordne("Wasser")
	r.expect("unbekannter Begriff -> nicht gefunden (nicht raten)", false, okU)
	_, okL := Ordne("")
	r.expect("leerer Begriff -> nicht gefunden", false, okL)

	// Feste Zahlen: Begriffs-IDs und Opcodes muessen exakt kanon.json entsprechen.
	var z struct {
		IDs struct {
			Begriffe []struct {
				ID      uint8  `json:"id"`
				Begriff string `json:"begriff"`
			} `json:"begriffe"`
		} `json:"ids"`
		Opcodes struct {
			Tabelle []struct {
				Op       uint8   `json:"op"`
				Objekt   string  `json:"objekt"`
				Operator string  `json:"operator"`
				Lesart   string  `json:"lesart"`
				Handler  *string `json:"handler"`
			} `json:"tabelle"`
		} `json:"opcodes"`
	}
	_ = json.Unmarshal(raw, &z) // Parsefehler wuerde oben schon gemeldet
	var idAbw []string
	for _, b := range z.IDs.Begriffe {
		st, ok := Ordne(b.Begriff)
		if !ok || st.ID() != b.ID {
			idAbw = append(idAbw, b.Begriff)
		}
	}
	r.expect("Begriffs-IDs == kanon.ids (je Begriff feste Zahl)", tuple{12, []string{}}, tuple{len(z.IDs.Begriffe), idAbw})
	var opAbw []string
	for _, e := range z.Opcodes.Tabelle {
		so, okO := Ordne(e.Objekt)
		sa, okA := Ordne(e.Operator)
		c := Opcode(e.Op)
		h := ""
		if e.Handler != nil {
			h = *e.Handler
		}
		if !okO || !okA || Op(Objekt(so.Pos), Operator(sa.Pos)) != c || c.Lesart() != e.Lesart || opcodeHandler[c] != h {
			opAbw = append(opAbw, fmt.Sprintf("%d %s", e.Op, e.Lesart))
		}
	}
	r.expect("Opcodes == kanon.opcodes (16 Paare, Zahl, Lesart, Handler)", tuple{16, []string{}}, tuple{len(z.Opcodes.Tabelle), opAbw})
	r.expect("Op(Zustand, Bravo) == 1, Lesart 'Zustand generieren'", tuple{1, "Zustand generieren"},
		tuple{int(Op(Zustand, Bravo)), Op(Zustand, Bravo).Lesart()})

	fn := func(f any) uintptr { return reflect.ValueOf(f).Pointer() }
	r.expect("gate[0] ist deltaReset (kanon: "+k.Gate["0"]+")", true, fn(gate[0]) == fn(deltaReset))
	r.expect("gate[1] ist deltaBinden (kanon: "+k.Gate["1"]+")", true, fn(gate[1]) == fn(deltaBinden))
	return r
}

// --- Checks: Maschine --------------------------------------------------

func checkMaschine() report {
	r := report{Saeule: "MASCHINE", Invariante: "Handles mit Generation, Capability-Bitset, Opcode-Dispatch O(1), ein Ergebnis je Msg"}
	alle := uint16(0xffff)
	m := neueMaschine()

	h, err := m.Neu(alle)
	r.expect("Neu: Slot 0, Generation 1", tuple{0, 1, nil}, tuple{int(h.Slot), int(h.Gen), err})
	_, ok := m.slot(h)
	r.expect("Lookup gueltiger Handle", true, ok)
	r.expect("Frei", true, m.Frei(h))
	_, ok = m.slot(h)
	r.expect("nach Frei: alter Handle ungueltig", false, ok)
	h2, _ := m.Neu(alle)
	_, okAlt := m.slot(h)
	r.expect("Slot wiederverwendet, neue Generation, alter Handle bleibt ungueltig (kein ABA)",
		tuple{true, true, false}, tuple{h2.Slot == h.Slot, h2.Gen > h.Gen, okAlt})
	r.expect("Dispatch mit altem Handle -> stale, kein Handler", AbwStale, m.Dispatch(Msg{Op: Op(Zustand, Alpha), H: h}).Abweisung)
	r.expect("Frei mit altem Handle -> false", false, m.Frei(h))

	voll := neueMaschine()
	var errV error
	for range maxObjekte + 1 {
		_, errV = voll.Neu(alle)
	}
	r.expect("mehr als maxObjekte -> ErrVoll", true, errors.Is(errV, ErrVoll))
	alt := neueMaschine()
	alt.slots[0].gen = math.MaxUint32 - 2
	ha, _ := alt.Neu(alle)
	alt.Frei(ha)
	r.expect("Generation am Ende -> Slot stillgelegt, nicht wieder vergeben", tuple{maxObjekte - 1, false},
		tuple{alt.freiTop, slices.Contains(alt.frei[:alt.freiTop], ha.Slot)})

	// Dispatch-Grenzen.
	ab := func(e Ergebnis) tuple { return tuple{e.Bit, int(e.Abweisung)} }
	r.expect("unbelegter Opcode (Zustand generieren) -> nicht_belegt", tuple{0, int(AbwNichtBelegt)},
		ab(m.Dispatch(Msg{Op: Op(Zustand, Bravo), H: h2})))
	r.expect("Opcode 16 -> ausserhalb", tuple{0, int(AbwOpcode)}, ab(m.Dispatch(Msg{Op: 16, H: h2})))
	nurIdent, _ := m.Neu(1 << Op(Zustand, Alpha))
	r.expect("Capability fehlt -> verboten", tuple{0, int(AbwVerboten)},
		ab(m.Dispatch(Msg{Op: Op(Transformation, Bravo), H: nurIdent, Arg: "x"})))
	r.expect("Capability vorhanden -> Handler laeuft", tuple{1, 0}, ab(m.Dispatch(Msg{Op: Op(Zustand, Alpha), H: nurIdent})))
	belegt := true
	for c := range Opcode(16) {
		belegt = belegt && (opcodeHandler[c] != "") == (reflect.ValueOf(handlers[c]).Pointer() != reflect.ValueOf(hNichtBelegt).Pointer())
	}
	r.expect("handlers belegt genau dort, wo kanon.opcodes einen Handler nennt", true, belegt)

	// Zyklus generieren -> validieren -> integrieren == T -> I -> S des Kerns.
	zyklus := func(raw any) (State, []Ergebnis) {
		mm := neueMaschine()
		hh, _ := mm.Neu(alle)
		var es []Ergebnis
		for _, op := range []Opcode{Op(Transformation, Bravo), Op(Information, Charlie), Op(Syncpunkt, Delta)} {
			es = append(es, mm.Dispatch(Msg{Op: op, H: hh, Arg: raw}))
		}
		return mm.slots[hh.Slot].state, es
	}
	gleichKern := true
	for _, raw := range stressPool {
		st, _ := zyklus(raw)
		ref := newState()
		_, _ = syncpunkt(&ref, tiSeriell(raw))
		gleichKern = gleichKern && st == ref
	}
	r.expect("generieren/validieren/integrieren == syncpunkt(tiSeriell) fuer alle Stress-Eingaben", true, gleichKern)
	st, es := zyklus("VALID_DATA")
	r.expect("Zyklus 'VALID_DATA' -> Bits 1,1,1, UPDATED", tuple{1, 1, 1, "UPDATED", "VALID_DATA"},
		tuple{es[0].Bit, es[1].Bit, es[2].Bit, st.Status, st.data()})
	st, es = zyklus("INVALID")
	r.expect("Zyklus 'INVALID' -> Bits 1,0,0, CLEAN, Grund block", tuple{1, 0, 0, "CLEAN", int(GrundBlock)},
		tuple{es[0].Bit, es[1].Bit, es[2].Bit, st.Status, int(es[2].Grund)})
	m3 := neueMaschine()
	h3, _ := m3.Neu(alle)
	vor := m3.slots[h3.Slot].state
	r.expect("integrieren ohne validieren -> ohne_info, Zustand unveraendert",
		tuple{int(AbwOhneInfo), true}, tuple{int(m3.Dispatch(Msg{Op: Op(Syncpunkt, Delta), H: h3}).Abweisung), m3.slots[h3.Slot].state == vor})
	m3.slots[h3.Slot].state.Tick = -1
	r.expect("identifizieren auf gebrochenem Zustand -> Bit 0", uint8(0), m3.Dispatch(Msg{Op: Op(Zustand, Alpha), H: h3}).Bit)

	// Owner-Goroutine: gleiche Ergebnisse, gleiche Reihenfolge wie seriell.
	msgs := func(mm *Maschine) []Msg {
		var out []Msg
		for i, raw := range stressPool {
			hh, _ := mm.Neu(alle)
			out = append(out,
				Msg{Op: Op(Transformation, Bravo), H: hh, Arg: raw},
				Msg{Op: Op(Information, Charlie), H: hh},
				Msg{Op: Op(Syncpunkt, Delta), H: hh},
				Msg{Op: Opcode(i % 17), H: hh})
		}
		return out
	}
	ms, mo := neueMaschine(), neueMaschine()
	var seriell []Ergebnis
	for _, msg := range msgs(ms) {
		seriell = append(seriell, ms.Dispatch(msg))
	}
	in := make(chan Msg)
	mm := msgs(mo)
	go func() {
		defer close(in)
		for _, msg := range mm {
			in <- msg
		}
	}()
	var owner []Ergebnis
	for e := range mo.Lauf(in) {
		owner = append(owner, e)
	}
	r.expect("Lauf (Owner-Goroutine) == seriell, ein Ergebnis je Msg", tuple{len(mm), true},
		tuple{len(owner), slices.EqualFunc(seriell, owner, func(a, b Ergebnis) bool {
			return a.Op == b.Op && a.H == b.H && a.Bit == b.Bit && a.Abweisung == b.Abweisung && a.Grund == b.Grund
		})})

	// Gegenprobe: ein Lookup ohne Generationsvergleich wuerde den alten Handle annehmen.
	naiv := m.slots[h.Slot].belegt
	r.expect("GEGENPROBE: Lookup ohne Generation nimmt veralteten Handle an, echter Lookup nicht",
		tuple{true, false}, tuple{naiv, okAlt})
	return r
}

// --- Checks: Plan ------------------------------------------------------

// checkPlan spielt ref/plan-faelle.json durch planMain und vergleicht die
// Ausgabe byte-genau. Beim Fall datei_fehlt weicht nur der Fehlertext der
// Lesefunktion ab (pipeline.py liegt nicht vor), verglichen werden dort
// Exit-Code und Zeilenanfang.
func checkPlan() report {
	r := report{Saeule: "PLAN", Invariante: "plan.py byte-genau: Kopf, Graph (fehlend, Zyklus), Hinweise, zulaessig/blockiert, Exit-Code"}
	raw, err := os.ReadFile("ref/plan-faelle.json")
	if err != nil {
		r.expect("ref/plan-faelle.json lesbar", nil, err.Error())
		return r
	}
	var ref struct {
		Faelle []struct {
			Name   string  `json:"name"`
			CSV    *string `json:"csv"`
			Exit   int     `json:"exit"`
			Stdout string  `json:"stdout"`
		} `json:"faelle"`
	}
	if err := json.Unmarshal(raw, &ref); err != nil {
		r.expect("ref/plan-faelle.json parsebar", nil, err.Error())
		return r
	}
	dir, aufraeumen, err := testDir()
	if err != nil {
		r.expect("tmp/ anlegbar", nil, err.Error())
		return r
	}
	defer aufraeumen()

	for _, f := range ref.Faelle {
		p := filepath.Join(dir, f.Name+".csv")
		if f.CSV != nil {
			if err := os.WriteFile(p, []byte(*f.CSV), 0o644); err != nil {
				r.expect(f.Name+": CSV geschrieben", nil, err.Error())
				continue
			}
		}
		var out bytes.Buffer
		code := planMain(p, &out)
		got := strings.Replace(out.String(), filepath.Clean(p), "{pfad}", 1)
		if f.CSV == nil {
			erste := strings.SplitN(got, "\n", 3)
			r.expect(f.Name+": Exit und Fehlerzeile", tuple{f.Exit, true},
				tuple{code, len(erste) > 1 && strings.HasPrefix(erste[1], "      FEHLER: ")})
			continue
		}
		r.expect(f.Name+": Exit-Code", f.Exit, code)
		r.expect(f.Name+": Ausgabe byte-genau", f.Stdout, got)
	}
	return r
}

// checkPlanZeit prueft die Zeitplanung an einem Graph mit bekannten
// Zahlen, die Claude-Grenze, Eingabefehler, das Dashboard und die
// Gleichheit der Zeitkonstanten mit profil.json.
func checkPlanZeit() report {
	r := report{Saeule: "PLAN-ZEIT", Invariante: "kritischer Pfad, Puffer, Aufwand; claude-Aufgabe <= 1 Sitzung (30 min); Konstanten == profil.json"}
	dir, aufraeumen, err := testDir()
	if err != nil {
		r.expect("tmp/ anlegbar", nil, err.Error())
		return r
	}
	defer aufraeumen()
	lauf := func(name, csv string) (int, string) {
		p := filepath.Join(dir, name)
		if err := os.WriteFile(p, []byte(csv), 0o644); err != nil {
			return -1, err.Error()
		}
		var out bytes.Buffer
		return planMain(p, &out), out.String()
	}
	kopf := "ID,Aufgabe,Abhängigkeit,Dauer,Werkzeug,Status\n"

	// A(roman 1 = 45) -> B(claude 1 = 30) und C(opencode 2 = 90) -> D(roman 1 = 45).
	zs := []planAufgabe{
		{ID: "A", Deps: []string{}, Dauer: 1, Werkzeug: "roman"},
		{ID: "B", Deps: []string{"A"}, Dauer: 1, Werkzeug: "claude"},
		{ID: "C", Deps: []string{"A"}, Dauer: 2, Werkzeug: "opencode"},
		{ID: "D", Deps: []string{"B", "C"}, Dauer: 1, Werkzeug: "roman"},
	}
	reihe, ende, pfad := zeitplanRechnen(zs, map[string]string{})
	zahlen := func(id string) tuple {
		for _, z := range reihe {
			if z.A.ID == id {
				return tuple{int(z.Start / 60), int(z.Ende / 60), int(z.Puffer() / 60)}
			}
		}
		return nil
	}
	r.expect("Projektende 180 min, kritischer Pfad A -> C -> D", tuple{180, []string{"A", "C", "D"}}, tuple{int(ende / 60), pfad})
	r.expect("B: Start 45, Ende 75, Puffer 60 (claude-Sitzung = 30 min)", tuple{45, 75, 60}, zahlen("B"))
	r.expect("C: Start 45, Ende 135, Puffer 0", tuple{45, 135, 0}, zahlen("C"))
	r.expect("D: Start 135 (wartet auf das spaetere Ende), Puffer 0", tuple{135, 180, 0}, zahlen("D"))
	reiheF, endeF, _ := zeitplanRechnen(zs, map[string]string{"A": "FERTIG"})
	r.expect("A FERTIG zaehlt 0: Ende 135, A nicht mehr im Plan", tuple{135, 3}, tuple{int(endeF / 60), len(reiheF)})

	code, out := lauf("ok.csv", kopf+"A,Basis,Start,1,roman,\nB,Gate,A,1,claude,\nC,Doku,A,2,opencode,\nD,Abnahme,B/C,\"1,0\",roman,\n")
	r.expect("CSV mit Dauer: Exit 0, Pfad und Aufwand im Text", tuple{0, true, true}, tuple{code,
		strings.Contains(out, "KRITISCHER PFAD (3:00, Untergrenze bei voller Parallelitaet): A -> C -> D"),
		strings.Contains(out, "GESAMTAUFWAND: 3:30 in 4 Aufgaben")})
	code, out = lauf("gross.csv", kopf+"A,Basis,Start,1,roman,\nB,zu gross,A,2,claude,\n")
	r.expect("claude-Aufgabe mit 2 Sitzungen -> Exit 3, FEHLER teilen", tuple{3, true},
		tuple{code, strings.Contains(out, "FEHLER: B: claude-Aufgabe mit 2 Sitzungen (1:00) > 1 Sitzung (30 min) - teilen")})
	code, out = lauf("dauer.csv", kopf+"A,Basis,Start,abc,roman,\n")
	r.expect("Dauer keine Zahl -> Exit 1", tuple{1, true}, tuple{code, strings.Contains(out, "FEHLER: A: Dauer 'abc' ist keine Zahl >= 0")})
	code, out = lauf("werkzeug.csv", kopf+"A,Basis,Start,1,chatgpt,\n")
	r.expect("unbekanntes Werkzeug -> Exit 1", tuple{1, true}, tuple{code, strings.Contains(out, "Werkzeug 'chatgpt' unbekannt")})
	code, out = lauf("status.csv", kopf+"A,Basis,Start,1,roman,FERTIG\nB,Gate,A,1,claude,\n")
	r.expect("Status aus Datei: A FERTIG -> B zulaessig", tuple{0, true, true}, tuple{code,
		strings.Contains(out, "[3/4] Status (aus der Datei, alle nicht genannten = OFFEN):\n      A = FERTIG"),
		strings.Contains(out, "ZULAESSIG (1):\n  B       Gate")})

	var dash bytes.Buffer
	codeD := planMain("idee-dashboard.jsonl", &dash)
	r.expect("idee-dashboard.jsonl: Graph ok, Zeitplan berechnet (Exit 0 oder 3)", tuple{true, true, true}, tuple{
		codeD == 0 || codeD == 3,
		strings.Contains(dash.String(), "ok: alle Abhaengigkeiten aufloesbar"),
		strings.Contains(dash.String(), "KRITISCHER PFAD")})

	raw, err := os.ReadFile("profil.json")
	if err != nil {
		r.expect("profil.json lesbar", nil, err.Error())
		return r
	}
	var prof struct {
		Budget struct {
			Zeit struct {
				Min int `json:"min_stunden"`
				Max int `json:"max_stunden"`
			} `json:"zeit_pro_woche"`
			Einheit struct {
				Roman  int `json:"roman_mit_cli_minuten"`
				Claude int `json:"claude_max_minuten"`
			} `json:"zeiteinheit"`
		} `json:"budget"`
	}
	if err := json.Unmarshal(raw, &prof); err != nil {
		r.expect("profil.json parsebar", nil, err.Error())
		return r
	}
	r.expect("Zeitkonstanten == profil.json (45 / 30 min, 48-72 h)",
		tuple{sitzungMinuten, claudeSitzungMinuten, wocheMinStunden, wocheMaxStunden},
		tuple{prof.Budget.Einheit.Roman, prof.Budget.Einheit.Claude, prof.Budget.Zeit.Min, prof.Budget.Zeit.Max})
	return r
}

// --- Checks: Prompt ----------------------------------------------------

func checkPrompt() report {
	r := report{Saeule: "PROMPT", Invariante: "Prompt 3+1 auf zwei Achsen; nur Bit 1 erreicht das Modell; Luecke nennt jeden Grund"}
	gut := func() Prompt {
		return Prompt{
			Kopf:     "Du bist Gaertner.",
			Koerper:  [][]string{{"apfel ist rot"}, {"birne ist gruen"}, {"kirsche ist klein"}},
			Fuss:     "Antworte in einem Satz.",
			Herkunft: []string{"apfel ist rot", "birne ist gruen", "kirsche ist klein"},
		}
	}
	pr := func(p Prompt) tuple { b, l := p.pruefe(); return tuple{b, l.Namen()} }

	r.expect("vollstaendig -> Bit 1, keine Luecke", tuple{1, []string{}}, pr(gut()))
	p := gut()
	p.Kopf = "  "
	r.expect("oben leer -> Bit 0, kopf", tuple{0, []string{"kopf"}}, pr(p))
	p = gut()
	p.Fuss = ""
	r.expect("unten leer -> Bit 0, fuss", tuple{0, []string{"fuss"}}, pr(p))
	p = gut()
	p.Koerper = [][]string{{}, {}, {}}
	r.expect("Koerper leer -> Bit 0, koerper", tuple{0, []string{"koerper"}}, pr(p))
	p = gut()
	p.Koerper[1] = append(p.Koerper[1], "apfel ist rot")
	r.expect("4 Zeilen -> Bit 0, zu_viel (|y| <= K)", tuple{0, []string{"zu_viel"}}, pr(p))
	p = gut()
	p.Koerper[2] = []string{"banane ist blau"}
	r.expect("Zeile ohne Herkunft -> Bit 0, fremd", tuple{0, []string{"fremd"}}, pr(p))
	p = gut()
	p.Koerper = append(p.Koerper, []string{})
	r.expect("4 Kategorien -> Bit 0, achse (zwei Motoren)", tuple{0, []string{"achse"}}, pr(p))
	p = gut()
	p.Koerper = p.Koerper[:2]
	r.expect("2 Kategorien -> Bit 0, achse (Motor vergessen)", tuple{0, []string{"achse"}}, pr(p))
	r.expect("mehrere Luecken gleichzeitig in fester Reihenfolge",
		tuple{0, []string{"kopf", "koerper", "fuss", "achse"}}, pr(Prompt{}))

	r.expect("Text: oben -> unten, im Koerper links -> rechts",
		"Du bist Gaertner.\n\napfel ist rot\nbirne ist gruen\nkirsche ist klein\n\nAntworte in einem Satz.", gut().Text())

	aufrufe := 0
	stub := func(prompt string) (string, error) { aufrufe++; return fmt.Sprintf("antwort(%d)", len(prompt)), nil }
	p = gut()
	p.Fuss = ""
	_, b0, _, _ := Motor(p, stub)
	r.expect("Motor Bit 0 -> Modell NICHT aufgerufen", tuple{0, 0}, tuple{b0, aufrufe})
	ant, b1, _, err := Motor(gut(), stub)
	r.expect("Motor Bit 1 -> Modell genau einmal, Antwort zurueck",
		tuple{1, 1, fmt.Sprintf("antwort(%d)", len(gut().Text())), nil}, tuple{b1, aufrufe, ant, err})

	// Verkabelung: zwei Eingaben, eine freigegeben.
	in := `{"kopf":"K","koerper":[["a"],[],[]],"fuss":"F","herkunft":["a"]}` + "\n" + `{"kopf":"","koerper":[]}` + "\n"
	var ausB, zielB bytes.Buffer
	err = promptStream(strings.NewReader(in), &ausB, &zielB)
	r.expect("promptStream ohne Fehler", nil, err)
	r.expect("aus: je Eingabe eine Zeile", 2, strings.Count(ausB.String(), "\n"))
	r.expect("ziel: nur der freigegebene Prompt", 1, strings.Count(zielB.String(), "\n"))
	r.expect("aus Zeile 2 nennt die Luecken",
		true, strings.Contains(ausB.String(), `"nr":2,"bit":0,"luecke":["kopf","koerper","fuss","achse"]`))
	return r
}

// --- Checks: Engine ----------------------------------------------------

// testDir legt ein Arbeitsverzeichnis unter ./tmp an (nichts ausserhalb
// des Projekts) und liefert es samt Aufraeumfunktion.
func testDir() (string, func(), error) {
	if err := os.MkdirAll("tmp", 0o755); err != nil {
		return "", nil, err
	}
	d, err := os.MkdirTemp("tmp", "beweis-*")
	if err != nil {
		return "", nil, err
	}
	return d, func() {
		os.RemoveAll(d)
		os.Remove("tmp") // scheitert still, solange tmp nicht leer ist
	}, nil
}

// datei liest die rohen Bytes, an liesText vorbei (fuer hash(datei)).
func datei(pfad string) string {
	b, err := os.ReadFile(pfad)
	if err != nil {
		return "<" + err.Error() + ">"
	}
	return string(b)
}

// pyLowerParitaet und pySplitParitaet gleichen gegen ref/py-*.json ab und
// liefern die ersten Abweichungen, sonst "".
func pyLowerParitaet() (einzeln, proben string, err error) {
	raw, err := os.ReadFile("ref/py-lower.json")
	if err != nil {
		return "", "", err
	}
	var ref struct {
		Einzeln map[string]string `json:"einzeln"`
		Proben  [][2]string       `json:"proben"`
	}
	if err := json.Unmarshal(raw, &ref); err != nil {
		return "", "", fmt.Errorf("ref/py-lower.json: %w", err)
	}
	var abw []string
	for r := range rune(unicode.MaxRune + 1) {
		if r >= 0xd800 && r <= 0xdfff {
			continue // Surrogate sind in Go-Strings nicht darstellbar
		}
		want, ok := ref.Einzeln[strconv.Itoa(int(r))]
		if !ok {
			want = string(r)
		}
		if got := pyLower(string(r)); got != want && len(abw) < 5 {
			abw = append(abw, fmt.Sprintf("U+%04X: %q statt %q", r, got, want))
		}
	}
	var pabw []string
	for _, p := range ref.Proben {
		if got := pyLower(p[0]); got != p[1] {
			pabw = append(pabw, fmt.Sprintf("%q: %q statt %q", p[0], got, p[1]))
		}
	}
	return strings.Join(abw, "; "), strings.Join(pabw, "; "), nil
}

func pySplitParitaet() (tabelle, proben string, err error) {
	raw, err := os.ReadFile("ref/py-splitlines.json")
	if err != nil {
		return "", "", err
	}
	var ref struct {
		Codepoints []rune               `json:"codepoints"`
		Proben     [][2]json.RawMessage `json:"proben"`
	}
	if err := json.Unmarshal(raw, &ref); err != nil {
		return "", "", fmt.Errorf("ref/py-splitlines.json: %w", err)
	}
	want := map[rune]bool{}
	for _, c := range ref.Codepoints {
		want[c] = true
	}
	for r := range rune(unicode.MaxRune + 1) {
		if pyIsLineBreak(r) != want[r] {
			tabelle = fmt.Sprintf("U+%04X", r)
			break
		}
	}
	var pabw []string
	for _, p := range ref.Proben {
		var in string
		var out []string
		if err := errors.Join(json.Unmarshal(p[0], &in), json.Unmarshal(p[1], &out)); err != nil {
			return "", "", fmt.Errorf("ref/py-splitlines.json: %w", err)
		}
		if got := pySplitlines(in); !slices.Equal(got, out) {
			pabw = append(pabw, fmt.Sprintf("%q: %q statt %q", in, got, out))
		}
	}
	return tabelle, strings.Join(pabw, "; "), nil
}

func checkPyParitaet() report {
	r := report{
		Saeule:     "PY-PARITAET",
		Invariante: "str.splitlines und str.lower wie Python (ref/py-*.json), ueber alle Codepoints",
	}
	tab, pro, err := pySplitParitaet()
	if err != nil {
		tab, pro = err.Error(), err.Error()
	}
	r.expect("pyIsLineBreak == Python splitlines-Trenner (U+0000..U+10FFFF)", "", tab)
	r.expect("pySplitlines == Python bei allen Proben", "", pro)
	ein, pro, err := pyLowerParitaet()
	if err != nil {
		ein, pro = err.Error(), err.Error()
	}
	r.expect("pyLower == Python str.lower je Codepoint", "", ein)
	r.expect("pyLower == Python bei Kontext-Proben (Final_Sigma, İ)", "", pro)
	return r
}

func checkB01() report {
	r := report{
		Saeule:     "BEWEIS-01",
		Invariante: "read_file(p) == read_file(p) bei unveraenderter Datei; kaputte Bytes -> Fehler, nicht falsches I",
	}
	dir, aufraeumen, err := testDir()
	if err != nil {
		r.expect("tmp/ anlegbar", nil, err.Error())
		return r
	}
	defer aufraeumen()
	p := filepath.Join(dir, "b01.txt")
	kaputt := filepath.Join(dir, "kaputt.txt")
	leer := filepath.Join(dir, "leer.txt")
	crlf := filepath.Join(dir, "crlf.txt")
	err = errors.Join(
		os.WriteFile(p, []byte("test"), 0o644),
		os.WriteFile(kaputt, []byte{'t', 0xff, 0xfe, 'x'}, 0o644), // Annahme: beliebige ungueltige UTF-8-Bytes
		os.WriteFile(leer, nil, 0o644),
		os.WriteFile(crlf, []byte("a\r\nb\rc"), 0o644),
	)
	r.expect("Testdateien geschrieben", nil, err)

	fi, err := os.Stat(p)
	r.expect("Z - Datei existiert, Bytes>0", true, err == nil && fi.Size() > 0)
	t1, err1 := liesText(p)
	r.expect("T - bytes->str dekodiert", "test", t1)
	r.expect("I - Inhalt korrekt", "test", t1)
	r.expect("S - len(return) == Zeichen der Datei", 4, utf8.RuneCountInString(t1))
	_, errK := liesText(kaputt)
	r.expect("Interferenz - kaputte Bytes -> ValueError", true, errors.Is(errK, ErrValue))
	t2, err2 := liesText(p)
	var gleich any = "<abweichend>"
	if t1 == t2 {
		gleich = t1
	}
	r.expect("INV - lies_text(p) == lies_text(p)", "test", gleich)
	var h any = "<abweichend>"
	if sha256Hex(t1) == sha256Hex(datei(p)) {
		h = sha256Hex(t1)
	}
	r.expect("INV - hash(return) == hash(datei)", "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08", h)
	r.expect("Lesen ohne Fehler", nil, errors.Join(err1, err2))

	// Go-spezifisch: B1-Randfaelle und Annahme Textmodus.
	tl, errL := liesText(leer)
	r.expect("leere Datei -> '' ohne Fehler", tuple{"", nil}, tuple{tl, errL})
	_, errF := liesText(filepath.Join(dir, "fehlt.txt"))
	r.expect("fehlende Datei -> ValueError (ErrDateiFehlt)", true, errors.Is(errF, ErrValue) && errors.Is(errF, ErrDateiFehlt))
	r.expect("kaputte Bytes -> ErrKaputt", true, errors.Is(errK, ErrKaputt))
	tc, _ := liesText(crlf)
	r.expect("Annahme Textmodus: \\r\\n und \\r -> \\n", "a\nb\nc", tc)

	// Gegenprobe: ein Leser, der Fehler verschluckt, faellt durch dieselbe Pruefung.
	naiv := func(p string) (string, error) { b, _ := os.ReadFile(p); return string(b), nil }
	_, errN := naiv(kaputt)
	r.expect("GEGENPROBE B1: Leser ohne UTF-8-Pruefung wird erkannt", false, errors.Is(errN, ErrValue))
	return r
}

func checkB02() report {
	r := report{Saeule: "BEWEIS-02", Invariante: "kern_1: I monoton, III Platte == Absicht, ZUSATZ idempotent"}
	dir, aufraeumen, err := testDir()
	if err != nil {
		r.expect("tmp/ anlegbar", nil, err.Error())
		return r
	}
	defer aufraeumen()
	soll := sha256Hex("test\nneuer fakt\n")

	// Annahme: Ausgangsbibliothek "test" ohne Zeilenende (01), deckt sep ab.
	p := filepath.Join(dir, "bib.txt")
	r.expect("Testdatei geschrieben", nil, os.WriteFile(p, []byte("test"), 0o640))
	vorher := datei(p)
	ok, err := kern1(p, "neuer fakt")
	nach := datei(p)
	r.expect("kern_1 ohne Fehler", nil, err)
	r.expect("I - Zeilen nachher == vorher + 1", len(fakten(vorher))+1, len(fakten(nach)))
	_, testDa := fakten(nach)["test"]
	r.expect("I - kein Fakt verloren ('test' noch da)", true, testDa)
	r.expect("III - kern_1 -> True (Platte == Absicht)", true, ok)
	r.expect("III - hash(datei) == hash(erwarteter Inhalt)", soll, sha256Hex(nach))

	ok2, err2 := kern1(p, "neuer fakt")
	nach2 := datei(p)
	r.expect("ZUSATZ - zweiter Aufruf -> False (kein doppeltes Tragen)", false, ok2)
	r.expect("ZUSATZ - Bibliothek unveraendert nach dup-Versuch", soll, sha256Hex(nach2))
	r.expect("ZUSATZ - Fakt steht genau 1x", 1, zaehle(nach2, "neuer fakt"))
	fehlt := filepath.Join(dir, "fehlt.txt")
	_, errF := kern1(fehlt, "x")
	r.expect("B1 - fehlende Datei -> ValueError", true, errors.Is(errF, ErrValue))
	_, errL := kern1(p, "   ")
	r.expect("leerer Fakt -> ValueError", true, errors.Is(errL, ErrValue))

	// Go-spezifisch.
	r.expect("zweiter Aufruf ohne Fehler", nil, err2)
	_, statErr := os.Stat(fehlt)
	r.expect("fehlende Datei wird nicht angelegt", true, errors.Is(statErr, os.ErrNotExist))
	r.expect("leerer Fakt: ErrFaktLeer, Bibliothek byte-identisch",
		tuple{true, soll}, tuple{errors.Is(errL, ErrFaktLeer), sha256Hex(datei(p))})
	fi, _ := os.Stat(p)
	r.expect("B3: Dateirechte bleiben erhalten (0640)", "-rw-r-----", fi.Mode().String())
	reste, _ := filepath.Glob(filepath.Join(dir, ".*.tmp-*"))
	r.expect("B3: keine Temp-Reste", 0, len(reste))
	ok3, _ := kern1(p, "  neuer fakt  ")
	r.expect("Fakt wird getrimmt verglichen (Idempotenz trotz Leerraum)", false, ok3)

	// Gegenproben: jeder Detektor muss eine absichtlich kaputte Variante fangen.
	g := filepath.Join(dir, "gegen.txt")
	verliertByte := func(pfad, text string) error { return schreibeAtomar(pfad, text[:len(text)-1]) }
	nurNeu := func(pfad, text string) error { return schreibeAtomar(pfad, "neuer fakt\n") }

	_ = os.WriteFile(g, []byte("test\n"), 0o644)
	okIII, errIII := kern1Mit(g, "neuer fakt", verliertByte)
	r.expect("GEGENPROBE III: Schreiber verliert 1 Byte -> kern_1 meldet False",
		tuple{false, nil}, tuple{okIII, errIII})
	_ = os.WriteFile(g, []byte("test\n"), 0o644)
	vorG := datei(g)
	_, _ = kern1Mit(g, "neuer fakt", nurNeu)
	r.expect("GEGENPROBE I: Schreiber verwirft alte Fakten -> monoton() False", false, monoton(vorG, datei(g)))
	r.expect("GEGENPROBE ZUSATZ: doppelter Fakt -> zaehle() == 2", 2, zaehle("test\nneuer fakt\nneuer fakt\n", "neuer fakt"))
	return r
}

func checkB04() report {
	r := report{
		Saeule:     "BEWEIS-04",
		Invariante: "kern_2 = kern_1 + holen: |y| <= K_MAX_ZETTEL = 3, unabhaengig von |Bibliothek|",
	}
	dir, aufraeumen, err := testDir()
	if err != nil {
		r.expect("tmp/ anlegbar", nil, err.Error())
		return r
	}
	defer aufraeumen()
	var errs []error
	bib := func(name string, zeilen []string) string {
		p := filepath.Join(dir, name)
		errs = append(errs, os.WriteFile(p, []byte(strings.Join(zeilen, "\n")+"\n"), 0o644))
		return p
	}
	apfel := func(n int) []string {
		z := make([]string, n)
		for i := range z {
			z[i] = fmt.Sprintf("apfel %d", i)
		}
		return z
	}
	hol := func(p, bedarf string) []string {
		y, err := holen(p, bedarf)
		errs = append(errs, err)
		return y
	}

	p200 := bib("b200.txt", apfel(200))
	y := hol(p200, "apfel")
	r.expect("II - 200 matchende Fakten -> |y| <= K", true, len(y) <= kMaxZettel)
	r.expect("II - |y| == K bei Ueberangebot", 3, len(y))
	r.expect("II - Bibliothek(2) -> |y| <= K", true, len(hol(bib("b2.txt", []string{"apfel rot", "apfel gruen"}), "apfel")) <= kMaxZettel)
	r.expect("II - Bibliothek(5000) -> |y| <= K  (gleiche Schranke)", true, len(hol(bib("b5000.txt", apfel(5000)), "apfel")) <= kMaxZettel)

	pk := bib("bk.txt", []string{"test"})
	yVor := hol(pk, "test fakt")
	_, errK := kern1(pk, "neuer fakt")
	errs = append(errs, errK)
	yNach := hol(pk, "test fakt")
	r.expect("II - |y_vor| <= K", true, len(yVor) <= kMaxZettel)
	r.expect("II - |y_nach| <= K", true, len(yNach) <= kMaxZettel)

	y2 := hol(p200, "apfel")
	r.expect("Retrieval - zweiter holen()-Aufruf frisch, nicht angehaengt", true, slices.Equal(y, y2) && len(y2) <= kMaxZettel)
	echt := true
	f200 := fakten(datei(p200))
	for _, z := range y {
		_, ok := f200[z]
		echt = echt && ok
	}
	r.expect("Retrieval - jeder Zettel ist eine echte Bibliothekszeile", true, echt)
	ph := bib("hund.txt", []string{"hund bellt", "katze schlaeft", "hund und katze zusammen"})
	r.expect("Relevanz - Fakt mit 2 Bedarfswoertern zuerst", "hund und katze zusammen", hol(ph, "hund katze")[0])
	r.expect("leerer Bedarf -> []", []string{}, hol(p200, "   "))
	r.expect("kein Treffer -> []  (|y|=0 <= K)", []string{}, hol(p200, "banane"))
	fehlt := filepath.Join(dir, "fehlt.txt")
	_, errF := holen(fehlt, "apfel")
	r.expect("B1 - fehlende Datei -> ValueError", true, errors.Is(errF, ErrValue))
	// "Determinismus - ... ['apfel 3', 'apfel 13', 'apfel 0']" bleibt offen:
	// Bibliothek und Bedarf dieses Laufs sind ohne test_*.py nicht bekannt.

	p := bib("k2.txt", []string{"test"})
	ang, kontext, err := kern2(p, "neuer fakt", "fakt")
	errs = append(errs, err)
	nach := datei(p)
	r.expect("I - Bibliothek waechst genau +1", 2, len(fakten(nach)))
	_, testDa := fakten(nach)["test"]
	r.expect("I - alter Fakt 'test' erhalten", true, testDa)
	r.expect("III - kern_1 in kern_2 -> True", true, ang)
	r.expect("III - hash(datei) == hash('test\\nneuer fakt\\n')", sha256Hex("test\nneuer fakt\n"), sha256Hex(nach))
	ang2, _, err := kern2(p, "neuer fakt", "fakt")
	errs = append(errs, err)
	r.expect("Idempotenz - zweiter kern_2 mit selbem Fakt -> angehaengt False", false, ang2)
	r.expect("Idempotenz - Fakt steht genau 1x", 1, zaehle(datei(p), "neuer fakt"))
	r.expect("II in kern_2 - |kontext| <= K", true, len(kontext) <= kMaxZettel)

	// Go-spezifisch.
	r.expect("alle Testaufrufe ohne Fehler", nil, errors.Join(errs...))
	r.expect("Gleichstand behaelt Bibliotheks-Reihenfolge", []string{"apfel 0", "apfel 1", "apfel 2"}, y)
	r.expect("Teilstring-Treffer, case-insensitiv (pyLower)", []string{"Apfelbaum"},
		hol(bib("baum.txt", []string{"Apfelbaum", "birne"}), "APFEL"))
	yF, errFB := holen(fehlt, "  ")
	r.expect("leerer Bedarf liest die Datei nicht (fehlt -> [] ohne Fehler)", tuple{[]string{}, nil}, tuple{yF, errFB})
	yG, _ := holenK(p200, "apfel", kMaxZettel+2)
	r.expect("GEGENPROBE II: holen mit K+2 -> Detektor |y| <= K meldet False", false, len(yG) <= kMaxZettel)
	return r
}

func checkS4() report {
	r := report{
		Saeule:     "INTEGRATION",
		Invariante: "DeltaExecutor schreibt akzeptierten Payload in den Zustand; laeuft NUR bei Bit=1",
	}
	tis := func(s *State, raw any) error {
		p := transform(raw)
		bit, g := inform(p)
		_, err := syncpunkt(s, paket{Payload: p, Bit: bit, Grund: g})
		return err
	}

	s := newState()
	err := func() error { _, err := deltaBinden(&s, "nutzlast"); return err }()
	r.expect("delta setzt data + status UPDATED", tuple{"nutzlast", "UPDATED"}, tuple{s.data(), s.Status})
	r.expect("deltaBinden ohne Fehler", nil, err)

	s = newState()
	err = tis(&s, "INVALID")
	r.expect("Bit=0: data NICHT gesetzt (kein APPLY)", nil, s.data())
	r.expect("Bit=0: status nicht UPDATED", true, s.Status != Updated)
	r.expect("Bit=0: T->I->S ohne Fehler", nil, err)
	l := newLoop(500*time.Millisecond, func() time.Duration { return 0 })
	res, err := l.Step("INVALID")
	r.expect("Bit=0: Rueckgabe meldet RESET", true, err == nil && strings.Contains(res.String(), "RESET"))

	s = newState()
	err = tis(&s, "gueltig")
	r.expect("Bit=1: data == payload", "gueltig", s.data())
	r.expect("Bit=1: status UPDATED", "UPDATED", s.Status)
	r.expect("Bit=1: T->I->S ohne Fehler", nil, err)

	// Go-spezifisch: Quirk 4, Original-Payload wird gebunden.
	s = newState()
	err = tis(&s, "  x  ")
	r.expect("Bit=1: Original-Payload gebunden, nicht getrimmt", tuple{"  x  ", true}, tuple{s.data(), s.HasData})

	// Go-spezifisch: Kausalitaetsbrueche am Gate, State bleibt unveraendert.
	s = State{Data: "alt", HasData: true, Tick: 3, LastPulse: time.Second, Status: Updated}
	vorher := s
	_, err = syncpunkt(&s, paket{Payload: 5, Bit: 1})
	r.expect("Bit=1 mit Nicht-string -> ErrDeltaTyp, State unveraendert",
		tuple{true, true}, tuple{errors.Is(err, ErrDeltaTyp), s == vorher})
	_, err = syncpunkt(&s, paket{Payload: "x", Bit: 2})
	r.expect("Bit=2 -> ErrBit, State unveraendert",
		tuple{true, true}, tuple{errors.Is(err, ErrBit), s == vorher})

	// Go-spezifisch: deltaReset auf konsistentem Zustand.
	s = State{Data: "muell", HasData: true, Tick: 7, LastPulse: 3 * time.Second, Status: Updated}
	alt, err := deltaReset(&s, nil)
	r.expect("deltaReset konsistent: kein Fehler", nil, err)
	r.expect("deltaReset konsistent: (None, 'CLEAN', 7), LastPulse erhalten",
		tuple{nil, "CLEAN", 7, true}, tuple{s.data(), s.Status, s.Tick, s.LastPulse == 3*time.Second})
	r.expect("deltaReset liefert Alt-Zustand", tuple{"muell", 7, "UPDATED"}, tuple{alt.Data, alt.Tick, alt.Status})

	// Go-spezifisch: deltaReset heilt einen inkonsistenten Zustand, ohne Fehler.
	s = State{Tick: -5, LastPulse: time.Second, Status: Wake | Updated}
	_, err = deltaReset(&s, nil)
	r.expect("deltaReset inkonsistent: geheilt ohne Fehler, tick 0, konsistent",
		tuple{nil, 0, "CLEAN", true}, tuple{err, s.Tick, s.Status, s.konsistent()})

	return r
}

// sameTI vergleicht Bit, Grund und Payload-repr positionsweise.
func sameTI(a, b []paket) bool {
	return slices.EqualFunc(a, b, func(x, y paket) bool {
		return x.Bit == y.Bit && x.Grund == y.Grund && pyRepr(x.Payload) == pyRepr(y.Payload)
	})
}

// --- Ref-Abgleich ----------------------------------------------------

var refDatei = map[string]string{
	"ZUSTAND":        "ref/S1-zustand.json",
	"TRANSFORMATION": "ref/S2-transformation.json",
	"INFORMATION":    "ref/S3-information.json",
	"INTEGRATION":    "ref/S4-integration.json",
	"INTERFERENZ":    "ref/S5-interferenz.json",
	"BEWEIS-01":      "ref/beweis/01-read_file-ztis.json",
	"BEWEIS-02":      "ref/beweis/02-kern_1.json",
	"BEWEIS-04":      "ref/beweis/04-kern_2.json",
}

// refLaden liest die Checks einer Referenzdatei: flach unter "checks" oder
// verschachtelt unter "saeulen".<name>."checks". Die Invariante zaehlt nur,
// wenn sie ein String ist (BEWEIS-02 fuehrt ein Objekt).
func refLaden(raw []byte) (inv *string, checks []check, err error) {
	var top struct {
		Invariante json.RawMessage `json:"invariante"`
		Checks     []check         `json:"checks"`
		Saeulen    map[string]struct {
			Checks []check `json:"checks"`
		} `json:"saeulen"`
	}
	if err := json.Unmarshal(raw, &top); err != nil {
		return nil, nil, err
	}
	var s string
	if json.Unmarshal(top.Invariante, &s) == nil {
		inv = &s
	}
	checks = top.Checks
	for _, name := range slices.Sorted(maps.Keys(top.Saeulen)) {
		checks = append(checks, top.Saeulen[name].Checks...)
	}
	return inv, checks, nil
}

// vergleicheRef gleicht r gegen die Python-Referenz ab. Verglichen werden
// saeule, invariante und je Ref-Check name, erwartet, gemessen, pass;
// geprueft_am bleibt aussen vor. Go-eigene Zusatz-Checks sind erlaubt.
func vergleicheRef(r report) (gleich int, offen, abweichend []string, err error) {
	raw, err := os.ReadFile(refDatei[r.Saeule])
	if err != nil {
		return 0, nil, nil, err
	}
	inv, refChecks, err := refLaden(raw)
	if err != nil {
		return 0, nil, nil, fmt.Errorf("%s: %w", refDatei[r.Saeule], err)
	}
	if inv != nil && *inv != r.Invariante {
		abweichend = append(abweichend, "invariante")
	}

	idx := make(map[string]check, len(r.Checks))
	for _, c := range r.Checks {
		idx[c.Name] = c
	}
	for _, want := range refChecks {
		got, ok := idx[want.Name]
		switch {
		case !ok:
			offen = append(offen, want.Name)
		case got != want:
			abweichend = append(abweichend, want.Name)
		default:
			gleich++
		}
	}
	return gleich, offen, abweichend, nil
}

func main() {
	lauf := flag.Bool("lauf", false, "JSONL-Schritte {\"t\",\"input\"} von stdin, Ergebnisse als JSONL nach stdout")
	phase := flag.String("phase", "a", "a = seriell, b = Owner-Goroutine + Bravo/Charlie-Stufen (nur mit -lauf)")
	interval := flag.Float64("interval", 0.5, "Chrono-Intervall in Sekunden (nur mit -lauf)")
	nStress := flag.Int("stress", 0, "nur Stress-Modus: Seeds je GOMAXPROCS-Wert")
	plan := flag.String("plan", "", "zulaessige naechste Aufgaben aus CSV (ID, Aufgabe, Abhängigkeit)")
	prompt := flag.Bool("prompt", false, "JSONL-Prompts {kopf,koerper,fuss,herkunft} von stdin pruefen")
	begriff := flag.String("begriff", "", "Begriff im Kanon nachschlagen: Layer, Position, Bedeutung")
	aus := flag.String("aus", "-", "Ergebnisse nach PFAD (\"-\" = stdout, nur mit -prompt)")
	ziel := flag.String("ziel", "", "freigegebene Prompts zusaetzlich nach PFAD (nur mit -prompt)")
	flag.Parse()

	switch {
	case *plan != "":
		os.Exit(planMain(*plan, os.Stdout))
	case *begriff != "":
		os.Exit(begriffMain(*begriff))
	case *prompt:
		if err := promptMain(*aus, *ziel); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	case *lauf:
		if err := laufStream(os.Stdin, os.Stdout, os.Stderr, sekunden(*interval), *phase); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	case *nStress > 0:
		os.Exit(checks(checkStress(*nStress)))
	default:
		os.Exit(checks(checkS1(), checkS2(), checkS3(), checkS4(), checkS5(),
			checkLauf("a"), checkLauf("b"), checkStress(20),
			checkPyParitaet(), checkB01(), checkB02(), checkB04(), checkKanon(), checkPrompt(), checkMaschine(), checkPlan(), checkPlanZeit()))
	}
}

// begriffMain gibt die feste Stelle eines Begriffs als JSON aus; Exit 1,
// wenn er nicht im Kanon steht.
func begriffMain(w string) int {
	if teile := strings.FieldsFunc(w, pyIsSpace); len(teile) == 2 {
		return paarMain(teile[0], teile[1])
	}
	st, ok := Ordne(w)
	if !ok {
		fmt.Fprintf(os.Stderr, "%q steht nicht im Kanon (kanon.json) - nicht raten, festlegen lassen\n", w)
		return 1
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	enc.SetEscapeHTML(false)
	if err := enc.Encode(map[string]any{
		"id":               st.ID(),
		"begriff":          st.Begriff,
		"layer":            layerNamen[st.Layer],
		"frage":            layerFragen[st.Layer],
		"position":         st.Pos + 1,
		"bedeutung":        posBedeutung[st.Pos],
		"taetigkeit":       taetigkeit(st),
		"gleiche_position": st.GleichePosition(),
	}); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	return 0
}

// paarMain gibt den festen Opcode eines Begriffspaars aus Objekt und
// Operator aus, in beliebiger Reihenfolge der beiden Woerter.
func paarMain(a, b string) int {
	sa, okA := Ordne(a)
	sb, okB := Ordne(b)
	if !okA || !okB {
		fmt.Fprintf(os.Stderr, "%q oder %q steht nicht im Kanon (kanon.json) - nicht raten\n", a, b)
		return 1
	}
	if sa.Layer == LayerOperator {
		sa, sb = sb, sa
	}
	if sa.Layer != LayerObjekt || sb.Layer != LayerOperator {
		fmt.Fprintf(os.Stderr, "ein Paar ist Objekt + Operator, nicht %s + %s\n", layerNamen[sa.Layer], layerNamen[sb.Layer])
		return 1
	}
	c := Op(Objekt(sa.Pos), Operator(sb.Pos))
	var handler any
	if h := opcodeHandler[c]; h != "" {
		handler = h
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	enc.SetEscapeHTML(false)
	if err := enc.Encode(map[string]any{
		"opcode":   c,
		"lesart":   c.Lesart(),
		"objekt":   objektWoerter[c.Objekt()],
		"operator": operatorWoerter[c.Operator()],
		"handler":  handler,
	}); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	return 0
}

// promptMain oeffnet -aus und -ziel und laesst promptStream laufen.
func promptMain(ausPfad, zielPfad string) (err error) {
	aus, err := oeffneAusgabe(ausPfad)
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, aus.Close()) }()

	var ziel io.Writer
	if zielPfad != "" {
		z, err := oeffneAusgabe(zielPfad)
		if err != nil {
			return err
		}
		defer func() { err = errors.Join(err, z.Close()) }()
		ziel = z
	}
	return promptStream(os.Stdin, aus, ziel)
}

// checks laeuft alle Saeulen, gleicht sie gegen ref/ ab und liefert den
// Exit-Code: 0 alles gruen, 1 Check oder Ref-Abweichung, 2 E/A-Fehler.
func checks(reports ...report) int {
	stamp := time.Now().Format("2006-01-02T15:04:05")
	codeHash := ""
	if src, err := os.ReadFile("Main.go"); err == nil {
		codeHash = sha256Hex(string(src))
	}

	ok := true
	for i := range reports {
		r := &reports[i]
		r.GeprueftAm = stamp
		r.CodeHash = codeHash
		ok = r.finish() && ok

		if _, ok := refDatei[r.Saeule]; !ok {
			fmt.Fprintf(os.Stderr, "%-15s go: %d checks, %s\n", r.Saeule, len(r.Checks), r.Ergebnis)
			continue
		}
		gleich, offen, abw, err := vergleicheRef(*r)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
		fmt.Fprintf(os.Stderr, "%-15s ref: %d gleich, %d offen, %d abweichend | go: %d checks, %s\n",
			r.Saeule, gleich, len(offen), len(abw), len(r.Checks), r.Ergebnis)
		for _, n := range abw {
			fmt.Fprintf(os.Stderr, "  ABWEICHEND: %s\n", n)
		}
		ok = ok && len(abw) == 0
	}

	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	enc.SetEscapeHTML(false)
	if err := enc.Encode(reports); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	if !ok {
		return 1
	}
	return 0
}
