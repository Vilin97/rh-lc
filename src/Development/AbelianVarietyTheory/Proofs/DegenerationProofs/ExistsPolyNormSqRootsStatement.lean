module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolyNormSqRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open Polynomial in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_normSq_roots' : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom F.asHom → PullPow F.asHom.left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  intro k _ _ B _ hB L hL F q hF hq
  let := hB.comm
  let ptEnd (Z : Over (Sp k)) : Module.End ℤ (Additive (Z ⟶ B)) :=
    (MonoidHom.toAdditive (IsMonHom.monoidHom F.asHom Z)).toIntLinearMap
  have ptEnd_pow {Z : Over (Sp k)} (x : Z ⟶ B) (n : ℕ) :
      (ptEnd Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (F ^ n).asHom) := by
    induction n with
    | zero => simp only [pow_zero, one_apply_eq_self, End.one_asHom, Category.comp_id]
    | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, ih, End.mul_asHom]
      exact congrArg Additive.ofMul (Category.assoc x (F ^ n).asHom F.asHom)
  have aeval_ptEnd {Z : Over (Sp k)} (x : Z ⟶ B) (P : ℤ[X]) :
      aeval (ptEnd Z) P (Additive.ofMul x) = Additive.ofMul (polyPt F P x) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply, polyPt, ← List.prod_toFinset _ List.nodup_range,
      List.toFinset_range, ofMul_prod]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, ptEnd_pow, ofMul_zpow]
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ (l : k) ≠ 0 := by
    by_cases h : ((2 : ℕ) : k) = 0
    · refine ⟨2 + 1, by norm_num, ?_⟩
      rw [Nat.cast_add, h]; simp
    · exact ⟨2, le_rfl, h⟩
  have hD (n : ℕ) := GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible k B hB
    (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
  obtain ⟨Q, Q1, Q2, Q3, Q4⟩ :=
    GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms k B hB L hL
  obtain ⟨r, hr⟩ := exists_monic_torsion (M := Additive (𝟙_ (Over (Sp k)) ⟶ B)) l
    (fun n => (hD n).1) (ptEnd _)
  have hT : ∀ f ∈ homSub B, ptEnd B f ∈ homSub B := fun f hf => by
    change IsMonHom (Additive.toMul f) at hf
    change IsMonHom (Additive.toMul f ≫ F.asHom)
    infer_instance
  let e : homSub B := ⟨Additive.ofMul (𝟙 B), inferInstanceAs (IsMonHom (𝟙 B))⟩
  let φ : Module.End ℤ (homSub B) := (ptEnd B).restrict hT
  have hev (x : 𝟙_ (Over (Sp k)) ⟶ B) (p : ℤ[X]) :
      aeval (ptEnd _) p (Additive.ofMul x) =
        Additive.ofMul (x ≫ Additive.toMul (aeval φ p e).1) := by
    have h := aeval_intertwine (evalPt x ∘ₗ (homSub B).subtype) φ (ptEnd _)
      (fun f => congrArg Additive.ofMul (Category.assoc x (Additive.toMul f.1) F.asHom)) p e
    have h' : (evalPt x ∘ₗ (homSub B).subtype) e = Additive.ofMul x :=
      congrArg Additive.ofMul (Category.comp_id x)
    rw [h'] at h
    exact h
  obtain ⟨P, hP, h0, hβ⟩ := GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector
    (homSub B) (fun f => Q (Additive.toMul f.1)) φ e q l r hl2
    (fun x y => by
      rw [sub_eq_add_neg]
      exact Q1 (Additive.toMul x.1) (Additive.toMul y.1))
    (fun x => Q2 _) (fun x hx => Subtype.ext (Q3 _ x.2 hx)) (fun x => Q4 _ q hq _)
    (fun n => by
      obtain ⟨χ, h1, h2, h3⟩ := hr n
      obtain ⟨g, hg, hg'⟩ := (hD n).2 (Additive.toMul (aeval φ χ e).1) (aeval φ χ e).2 fun x hx =>
        (hev x χ).symm.trans (h3 (Additive.ofMul x) hx)
      exact ⟨χ, ⟨Additive.ofMul g, hg⟩, h1, h2, Subtype.ext hg'⟩)
  refine ⟨P, hP, hβ, fun x => ?_⟩
  have h := (aeval_ptEnd x P).symm.trans (hev x P)
  rw [h0] at h
  exact h.trans (MonObj.comp_one x)
