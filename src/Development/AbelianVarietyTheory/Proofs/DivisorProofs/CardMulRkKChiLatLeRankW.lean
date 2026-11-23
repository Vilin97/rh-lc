module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe

section

@[expose] public section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add (f := _), smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.CovolRank

theorem comap_val_finite {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) [FiniteDimensional K C] :
    FiniteDimensional K (C.comap A.val.toLinearMap) ∧
      Module.finrank K (C.comap A.val.toLinearMap) ≤ Module.finrank K C := by
  let f : C.comap A.val.toLinearMap →ₗ[K] C :=
    LinearMap.codRestrict C (A.val.toLinearMap ∘ₗ (C.comap A.val.toLinearMap).subtype)
      fun y => Submodule.mem_comap.1 y.2
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg (fun z : C => (z : B)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : FiniteDimensional K (C.comap A.val.toLinearMap) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

theorem finrank_span_le_of_map {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) (hC : C ≤ Subalgebra.toSubmodule A) {O : Type} [CommRing O] [Module O C]
    (L : Submodule O C) (N : Submodule K A) [FiniteDimensional K N]
    (hL : ∀ F ∈ L, (⟨(F : B), hC F.2⟩ : A) ∈ N) :
    Module.finrank K (Submodule.span K (L : Set C)) ≤ Module.finrank K N := by
  let Φ : C →ₗ[K] A := LinearMap.codRestrict (Subalgebra.toSubmodule A) C.subtype fun y => hC y.2
  have hΦ : Function.Injective Φ := fun a b hab => by
    have h := congrArg (fun z : A => (z : B)) hab
    exact Subtype.ext h
  have hle : Submodule.span K (L : Set C) ≤ N.comap Φ := by
    rw [Submodule.span_le]
    intro F hF
    exact hL F hF
  let ψ : Submodule.span K (L : Set C) →ₗ[K] N :=
    LinearMap.codRestrict N (Φ ∘ₗ (Submodule.span K (L : Set C)).subtype) fun y => hle y.2
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext (hΦ (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hψ

end GlobalTheory.CovolRank

namespace GlobalTheory.CovolRank

set_option maxHeartbeats 4000000 in
theorem card_mul_rkK_chiLat_le_rankW : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E), Even G.2 → Even W.2 → KeepsCusp U G → KeepsCusp U W → GoodW U x V dict G → GoodW U x V dict (G + W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ rankW U (G + W) := by
  classical
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hKG hKW hgG hgGW χ u hdet
  have hsec : ∀ G' : WTZ E, cuspW Xo c U G' ≤ Subalgebra.toSubmodule (secRing Xo c) :=
    fun G' f hf => GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ G' hf)
  have hfin : ∀ G' : WTZ E, GlobalTheory.AllWt.GoodW U x V dict G' → FiniteDimensional c.F (cuspW Xo c U G') := by
    intro G' hg
    obtain ⟨n, ⟨b, _⟩, _⟩ := hg.1.some
    exact Module.Finite.of_basis b
  have := hfin G hgG
  have := hfin (G + W) hgGW
  obtain ⟨hVs, -⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U G)
  obtain ⟨hVp, hVp'⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U (G + W))
  let uR : secRing Xo c := ⟨u, hsec W u.2⟩
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) uR).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have hc := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA uR
    refine mem_nonZeroDivisors_iff_left.mpr fun y hy => ?_
    apply Subtype.ext
    have h0 : levDet Xo c S u * (y : Rul Xo c) = 0 := by
      rw [← hc]; exact congrArg Subtype.val hy
    exact hdet _ y.2 h0

  let ι : secRing Xo c →ₗ[c.F] Rul Xo c := (secRing Xo c).val.toLinearMap
  let N : Submodule c.F (secRing Xo c) :=
    (cuspW Xo c U G).comap ι ⊓ GlobalTheory.LevDesc.eigen (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) χ
  have key := (GlobalTheory.finrank_le_card_mul_finrank_eigenspace_le S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ uR hdet'
    ⊥ ((cuspW Xo c U G).comap ι) ((cuspW Xo c U (G + W)).comap ι) N
    (fun h y hy => hKG h _ hy)
    (fun h y hy => by
      rw [Submodule.mem_bot] at hy
      subst hy
      rw [zero_mul]; exact Submodule.zero_mem _)
    (fun h y hy => GlobalTheory.SlopeRec.mul_mem_cuspW hG hW hy (hKW h _ u.2))
    (fun y => Submodule.mem_inf)).2
  have : FiniteDimensional c.F N := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ Module.finrank c.F N :=
    finrank_span_le_of_map (secRing Xo c) (cuspW Xo c U G) (hsec G) _ N fun F hF =>
      ⟨F.2, fun h => Subtype.ext (hF.2 h)⟩
  have e : rankW U (G + W) = Module.finrank c.F (cuspW Xo c U (G + W)) := by
    rw [rankW, Formalism.HN.rkK, hgGW.2.2, finrank_top]
  calc Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ)
      ≤ Fintype.card S * Module.finrank c.F N := Nat.mul_le_mul_left _ h1
    _ ≤ Module.finrank c.F ((cuspW Xo c U (G + W)).comap ι) := key
    _ ≤ rankW U (G + W) := e ▸ hVp'

end GlobalTheory.CovolRank
end
end
