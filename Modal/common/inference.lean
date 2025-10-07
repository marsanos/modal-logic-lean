/- Two structures for inference rules. I find this more convenient than
having a single structure with a list of premises, which would be
more difficult to deal with in Lean. -/


structure InferenceRule1 (φ : Type) where
  premise : φ
  conclusion : φ

structure InferenceRule2 (φ : Type) where
  premise1 : φ
  premise2 : φ
  conclusion : φ
