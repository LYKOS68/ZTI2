# External-domain probe: telemetry intake gate

## Question

Can the existing ZTI2 validation and state-transition path be reused for
telemetry-event intake without changing the production kernel?

## Probe

The tests apply the existing `inform -> syncpunkt -> Delta` path to a
JSON-formatted telemetry event:

- A non-empty JSON string is accepted and bound unchanged; state becomes
  `UPDATED`.
- Non-string, empty, whitespace-only, blocked-marker, and over-length inputs
  produce gate bit 0; the previous payload is cleared and state becomes
  `CLEAN`.
- A gate bit outside 0/1 is rejected without state mutation.

No production code is changed.

## Scope and limits

This demonstrates reuse of the existing generic gate contract in a second
application context. It does not validate JSON syntax, telemetry schemas,
measurement units, timestamps, device identity, authorization, anomaly
thresholds, or safety constraints. Those domain rules are not implemented by
the current `inform` function and must not be attributed to ZTI2.

A passing test would be evidence of cross-context reuse, not proof that the
whole ZTIS model is universal.

## Run

```sh
go test Main.go ztis_external_telemetry_gate_test.go
```

The tests have not been executed in this environment; record their actual
result before merging.
