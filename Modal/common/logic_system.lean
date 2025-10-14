import Mathlib.Data.Set.Defs

universe u

/-- A class representing a general logical system. -/
class logic_system (Formula : Type u) (Model : Type u) where
  is_formula : Formula → Prop -- syntactically valid formulas
  is_provable : Set Formula → Formula → Prop -- proof system
  is_model : Model → Prop -- what counts as a model (e.g., Kripke, valuation, etc.)

-- Example usage:
-- instance : logic_system my_formula_type my_model_type := ...
