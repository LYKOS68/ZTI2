# External-domain probe: document intake gate

## Question

Can an existing ZTI2 core path be reused in a domain that is not prompt
validation or task planning, without changing the production kernel?

## Probe

This experiment applies the current `inform -> syncpunkt -> Delta` path to
document intake:

1. A non-empty document payload that does not match the existing block markers
   is accepted by `inform`.
2. Gate bit 1 reaches `deltaBinden`; the original payload is bound unchanged
   and the state becomes `UPDATED`.
3. Empty, whitespace-only, and blocked-marker payloads produce gate bit 0.
   Gate bit 0 reaches `deltaReset`; the previous payload is cleared and the
   state becomes `CLEAN`.
4. A gate bit outside 0/1 is rejected without changing the state.

The probe is implemented as tests against the existing functions in
`Main.go`. It adds no production code and does not duplicate the ZTI2 kernel.

## What this demonstrates

It demonstrates that the existing generic validation and state-transition
mechanism can be exercised in a separate application context without changing
its implementation.

## What it does not demonstrate

This is not a complete document approval system. The current `inform`
function only checks the rules already present in ZTI2 (string type, empty
value, the exact blocked markers, and maximum length). It does not verify
document format, signatures, identity, permissions, provenance, or human
approval. Those rules must not be silently attributed to ZTI2.

Therefore, a passing probe is evidence of reuse of the current gate contract,
not proof that the entire ZTIS model is universal.

## Run

From the repository root, with the Go version required by the project:

```sh
go test Main.go ztis_external_document_gate_test.go
```

The test result must be recorded from an actual run; this change itself does
not claim that the tests have already passed.
