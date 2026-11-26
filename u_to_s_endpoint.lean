import u_step_refinement

/- Canonical pure-S encoding of a U(3,11) configuration at the root hub.
   The constructive bidirectional halting theorem `constructive_fixed_u_to_s_halting`
   is proved with zero `Classical.choice` in `formal_controller/constructive_endpoint.lean`. -/

def sEncodeU (initial : UConfig) : Term :=
  canonicalRoot (initialRecords (encodeUConfig initial)) 1 (depthBase 1) (depthJunk 0)

#print axioms sEncodeU
