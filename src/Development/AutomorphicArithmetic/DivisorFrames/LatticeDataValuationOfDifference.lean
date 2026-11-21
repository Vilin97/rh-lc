import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.ValGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

private theorem skewK {K : Type} [CommRing K] (u v : K ⊗[ℤ] Dw.La) :
    Dw.EF.baseChange K u v = -Dw.EF.baseChange K v u := by
  have skew : ∀ x y : Dw.La, Dw.EF x y = -Dw.EF y x := fun x y => by
    have := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
  | tmul k x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u u' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
    | tmul k' x' =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, skew x x', neg_smul, mul_comm]

private theorem adjK {K : Type} [CommRing K] (o : 𝓞 E) (u v : K ⊗[ℤ] Dw.La) :
    Dw.EF.baseChange K (((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange K u) v =
      Dw.EF.baseChange K u (((LinearMap.lsmul (𝓞 E) Dw.La (H.bar o)).restrictScalars ℤ).baseChange K v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | tmul k x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u u' h h' => simp only [map_add, h, h']
    | tmul k' x' =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, LinearMap.restrictScalars_apply,
        LinearMap.lsmul_apply]
      rw [Dw.adj]

private theorem torsionFree : Module.IsTorsionFree ℤ Dw.La :=
  Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)

private theorem expand : ∃ (n : ℕ) (e y : Fin n → Dw.La), ∀ (K : Type) [CommRing K] (w : K ⊗[ℤ] Dw.La),
    w = ∑ m, Dw.EF.baseChange K (1 ⊗ₜ y m) w • ((1 : K) ⊗ₜ[ℤ] e m) := by
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI := torsionFree Dw
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  choose y hy using fun m' : Fin N => Dw.unimod.2 (a.coord m')
  refine ⟨N, a, y, fun K _ w => ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u u' h h' =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← h, ← h']
  | tmul k x =>
    conv_lhs => rw [← a.sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.BilinForm.baseChange_tmul, hy, Module.Basis.coord_apply, TensorProduct.smul_tmul', _root_.one_mul,
      smul_eq_mul, _root_.mul_one, TensorProduct.smul_tmul]

private theorem bar_bar' (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

private theorem mem_span_iff {K : Type} [NormedField K] [IsUltrametricDist K] (w : K ⊗[ℤ] Dw.La) :
    w ∈ Submodule.span ↥(intO K) (Set.range fun a : Dw.La => (1 : K) ⊗ₜ[ℤ] a) ↔ ∀ b, ‖pr Dw w b‖ ≤ 1 := by
  constructor
  · intro hw b
    change pr Dw w b ∈ intO K
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [pr, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, zsmul_eq_mul]
      exact intCast_mem _ _
    | zero => simp only [pr, map_zero, LinearMap.zero_apply]; exact zero_mem _
    | add x y _ _ hx hy => simp only [pr, map_add, LinearMap.add_apply]; exact add_mem hx hy
    | smul c x _ hx =>
      have : pr Dw (c • x) b = (c : K) * pr Dw x b := by
        change pr Dw ((c : K) • x) b = _
        simp only [pr, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [this]
      exact mul_mem c.2 hx
  · intro h
    obtain ⟨n, e, y, he⟩ := expand Dw
    rw [he K w]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hm : Dw.EF.baseChange K (1 ⊗ₜ y m) w ∈ intO K := by
      rw [skewK]
      exact neg_mem (show pr Dw w (y m) ∈ intO K from h (y m))
    exact Submodule.smul_mem _ (⟨_, hm⟩ : ↥(intO K)) (Submodule.subset_span ⟨e m, rfl⟩)

private theorem mem_of_perp {K : Type} [Field K] (σ s : 𝓞 E →+* K) (hs : ∀ o, s o = σ (H.bar o)) (w : K ⊗[ℤ] Dw.La)
    (hw : ∀ x, IsEigL Dw s x → Dw.EF.baseChange K w x = 0) :
    w ∈ Submodule.span K {u : K ⊗[ℤ] Dw.La | ∃ (o : 𝓞 E) (u' : K ⊗[ℤ] Dw.La),
      u = ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange K u' - σ o • u'} := by
  by_contra hn
  obtain ⟨f, hf, hU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨n, e, y, he⟩ := expand Dw
  set x : K ⊗[ℤ] Dw.La := ∑ m, f ((1 : K) ⊗ₜ[ℤ] e m) • ((1 : K) ⊗ₜ[ℤ] y m) with hx
  have hfx : ∀ u, f u = -Dw.EF.baseChange K u x := by
    intro u
    rw [← skewK]
    conv_lhs => rw [he K u]
    simp only [hx, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  apply hf
  rw [hfx, hw x, neg_zero]
  intro o
  rw [← sub_eq_zero, he K (_ - _)]
  refine Finset.sum_eq_zero fun m _ => ?_
  have h0 : f (((LinearMap.lsmul (𝓞 E) Dw.La (H.bar o)).restrictScalars ℤ).baseChange K ((1 : K) ⊗ₜ[ℤ] y m)
      - σ (H.bar o) • ((1 : K) ⊗ₜ[ℤ] y m)) = 0 := by
    rw [← Submodule.mem_bot K, ← hU]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨H.bar o, _, rfl⟩)
  rw [hfx, neg_eq_zero, map_sub, LinearMap.sub_apply, adjK, bar_bar', map_smul, LinearMap.smul_apply] at h0
  rw [map_sub, map_smul, hs, h0, zero_smul]

end SlopeTestRemainingChoices
