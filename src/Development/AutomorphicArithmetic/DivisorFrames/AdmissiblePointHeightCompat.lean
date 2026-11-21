module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnitTriAndDiagCoeffMulEqOfCarries
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsStalkPointLift
public import Development.AutomorphicArithmetic.DivisorFrames.MetricLetterHeight
public import Development.AutomorphicArithmetic.DivisorFrames.GenericStalkSectionUnit
public import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleModelValuationAlt
public import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleFlagValuation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {k : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Pad.Letter Dw}

private theorem top_le_gen {X X' : Scheme.{0}} [IsIntegral X] {q : X ⟶ X'} {V : X'.Opens}
    (h : genericPoint X ∈ q ⁻¹ᵁ V) : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ q) ⁻¹ᵁ V := by
  refine (Scheme.preimage_eq_top_of_closedPoint_mem _ ?_).ge
  have e : (X.fromSpecStalk (genericPoint X) ≫ q) (closedPoint (X.presheaf.stalk (genericPoint X))) =
      q (genericPoint X) := (Scheme.Hom.comp_apply _ _ _).trans (congrArg q Scheme.fromSpecStalk_closedPoint)
  exact e ▸ h

private theorem exists_sec (M : LineModel Z k st x) {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Z.X) (a : Fin Z.m)
    (ha : genericPoint X ∈ q ⁻¹ᵁ (Z.U a).1) (c₀ : X.functionFieldˣ) :
    ∃ t : (M.L.lb.pull q).ι → X.functionFieldˣ, IsRatSec (M.L.lb.pull q) t ∧
      ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) → (t i : X.functionField) *
        valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.r a (i PUnit.unit)).val = c₀ := by
  let ρ : Fin M.L.n → X.functionField := fun i =>
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.r a i).val
  have n : ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U i → ρ i ≠ 0 := fun i hi =>
    left_ne_zero_of_mul_eq_one (Pull.valF_mul_inv (F := X.functionField)
      (top_le_gen (V := (Z.U a).1 ⊓ M.L.U i) ⟨ha, hi⟩) (M.r a i))
  let t : (M.L.lb.pull q).ι → X.functionFieldˣ := fun i =>
    if h : ρ (i PUnit.unit) ≠ 0 then c₀ * (Units.mk0 _ h)⁻¹ else 1
  have ht : ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) → (t i : X.functionField) * ρ (i PUnit.unit) = c₀ :=
    fun i hi => by
      have := n _ hi
      simp only [t, dif_pos this, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
  refine ⟨t, fun i j hij => ?_, ht⟩
  have le : (M.L.lb.pull q).U i ⊓ (M.L.lb.pull q).U j ≤ q ⁻¹ᵁ (M.L.U (i PUnit.unit) ⊓ M.L.U (j PUnit.unit)) :=
    fun x hx => ⟨LB.pull_U_le q i hx.1, LB.pull_U_le q j hx.2⟩
  have e₁ := M.trans X.functionField (X.fromSpecStalk (genericPoint X) ≫ q) a (i PUnit.unit) (j PUnit.unit)
    (top_le_gen ⟨ha, le hij⟩)
  have e₂ : fnOf _ hij ((M.L.lb.pull q).g i j).val = valF (F := X.functionField)
      (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.L.g (i PUnit.unit) (j PUnit.unit)).val := by
    rw [(UpperTheory.generic_stalk_section_unit X Z.X q _ _).1 (le hij), InducedPull.val_pull_g M.L.lb q i j le]
    exact fnOf_resG le hij _
  refine mul_right_cancel₀ (n _ (le hij).1) ?_
  rw [ht i (le hij).1, e₂, ← ht j (le hij).2]
  simp only [ρ]
  rw [e₁]
  ring

private theorem bc_comp {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (χ : B →+* C) (ρ : A →+* B) (u : Vecs Dw t A) :
    (fun σ m => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (χ.comp ρ)) ≫ u σ m) = Vecs.bc χ (Vecs.bc ρ u) := by
  funext σ m
  rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext w <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

private theorem succ_mul_succ_sub_one_div_succ {K : Type} [Field K] {c u r r' t t' : K} (hc : c ≠ 0) (ht : t' ≠ 0) (e₁ : u * r = r')
    (e₂ : t * r = c) (e₃ : t' * r' = c) : u = t / t' := by
  rw [eq_div_iff ht]
  refine mul_right_cancel₀ (right_ne_zero_of_mul (e₂ ▸ hc)) ?_
  rw [e₂, ← e₃, ← e₁]
  ring

end SlopeTestRemainingChoices
