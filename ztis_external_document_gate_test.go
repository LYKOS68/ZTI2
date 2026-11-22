package main

import "testing"

// This is an external-domain probe: reuse the existing ZTI2 validation and
// sync gate for document intake without changing the production kernel.
// It tests the current generic gate contract, not document authenticity,
// signatures, authorization, or business-specific document rules.

func TestExternalDocumentIntakeGateAcceptsValidPayload(t *testing.T) {
	raw := "DOC-ID: 4711\nSTATE: READY\nCONTENT: Example document"

	bit, reason := inform(raw)
	if bit != 1 || reason != 0 {
		t.Fatalf("valid document payload: inform() = (%d, %v), want (1, 0)", bit, reason)
	}

	state := newState()
	if _, err := syncpunkt(&state, paket{Payload: raw, Bit: bit, Grund: reason}); err != nil {
		t.Fatalf("syncpunkt() rejected valid payload: %v", err)
	}
	if !state.HasData || state.Data != raw || state.Status != Updated {
		t.Fatalf("accepted payload not bound unchanged: state = %+v", state)
	}
}

func TestExternalDocumentIntakeGateResetsRejectedPayloads(t *testing.T) {
	cases := []struct {
		name string
		raw  string
	}{
		{name: "empty", raw: ""},
		{name: "whitespace only", raw: " \t\n "},
		{name: "blocked marker INVALID", raw: "INVALID"},
		{name: "blocked marker CORRUPT", raw: "CORRUPT"},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			bit, reason := inform(tc.raw)
			if bit != 0 || reason == 0 {
				t.Fatalf("rejected payload: inform() = (%d, %v), want (0, nonzero)", bit, reason)
			}

			state := State{Data: "previous document", HasData: true, Status: Updated}
			if _, err := syncpunkt(&state, paket{Payload: tc.raw, Bit: bit, Grund: reason}); err != nil {
				t.Fatalf("syncpunkt() failed to reset rejected payload: %v", err)
			}
			if state.HasData || state.Data != "" || state.Status != Clean {
				t.Fatalf("rejected payload was not reset: state = %+v", state)
			}
		})
	}
}

func TestExternalDocumentIntakeGateRejectsInvalidGateBitWithoutMutation(t *testing.T) {
	state := State{Data: "keep this document", HasData: true, Tick: 7, Status: Updated}
	before := state

	_, err := syncpunkt(&state, paket{Payload: "DOC-ID: 4711", Bit: 2})
	if err == nil {
		t.Fatal("syncpunkt() accepted gate bit 2; want an error")
	}
	if state != before {
		t.Fatalf("invalid gate bit mutated state: before=%+v after=%+v", before, state)
	}
}
