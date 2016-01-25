c11_orig.cat:
- Uses total SC order.
- Adapted from POPL'16 version *not* to use init writes.

c11_simp.cat:
- Uses partial SC order.

c11_complus.cat:
- Same as c11_simp, but uses "hb | com+" in partial SC constraint, which may make SC fences strong enough to kill IRIW while not invalidating compilation schemes.