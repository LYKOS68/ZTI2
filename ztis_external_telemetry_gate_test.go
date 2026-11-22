package main

import (
	"strings"
	"testing"
)

// External-domain probe: telemetry ingestion reuses the existing ZTI2
// inform -> syncpunkt -> Delta path without changing the production kernel.
// These tests cover the current generic gate contract only. They do not
// validate telemetry schemas, units, timestamps, device identity, or safety.

func TestExternalTelemetryGateAcceptsNonEmptyEvent(t *testing.T) {
	raw := `{"device":"sensor-17","metric":"temperature","value":21.4,"unit":"C"}`

	bit, reason := inform(raw)
	if bit != 1 || reason != 0 {
		t.Fatalf("telemetry event: inform() = (%d, %v), want (1, 0)", bit, reason)
	}

	state := newState()
	if _, err := syncpunkt(&state, paket{Payload: raw, Bit: bit, Grund: reason}); err != nil {
		t.Fatalf("syncpunkt() rejected telemetry event: %v", err)
	}
	if !state.HasData || state.Data != raw || state.Status != Updated {
		t.Fatalf("event was not bound unchanged: state = %+v", state)
	}
}

func TestExternalTelemetryGateResetsInvalidGenericInputs(t *testing.T) {
	cases := []struct {
		name string
		raw  any
	}{
		{name: "non-string value", raw: 42},
		{name: "empty event", raw: ""},
		{name: "whitespace event", raw: " \t\n "},
		{name: "blocked marker", raw: "CORRUPT"},
		{name: "over maximum length", raw: strings.Repeat("x", maxLen+1)},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			bit, reason := inform(tc.raw)
			if bit != 0 || reason == 0 {
				t.Fatalf("invalid generic input: inform() = (%d, %v), want (0, nonzero)", bit, reason)
			}

			state := State{Data: "previous telemetry event", HasData: true, Status: Updated}
			if _, err := syncpunkt(&state, paket{Payload: tc.raw, Bit: bit, Grund: reason}); err != nil {
				t.Fatalf("syncpunkt() failed to reset rejected input: %v", err)
			}
			if state.HasData || state.Data != "" || state.Status != Clean {
				t.Fatalf("rejected input was not reset: state = %+v", state)
			}
		})
	}
}

func TestExternalTelemetryGateRejectsOutOfRangeBitWithoutMutation(t *testing.T) {
	state := State{Data: "keep previous event", HasData: true, Tick: 3, Status: Updated}
	before := state

	_, err := syncpunkt(&state, paket{Payload: "telemetry", Bit: 2})
	if err == nil {
		t.Fatal("syncpunkt() accepted gate bit 2; want an error")
	}
	if state != before {
		t.Fatalf("invalid gate bit mutated state: before=%+v after=%+v", before, state)
	}
}
