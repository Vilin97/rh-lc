module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfGermEqZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.Vanishing.ProdNe

theorem eq_zero_of_germ_eq_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    {p : Y ⟶ Sp k} {B : LB Y} (hc : ∀ z : Y, ∃ j, z ∈ B.U j) (f : H0 p B ⊤) (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) (h0 : H0.germ i y (show y ∈ (⊤ : Y.Opens) from trivial) hi f = 0) : f = 0 := by
  have hi0 : f.loc i = 0 := by
    apply germ_injective_of_isIntegral Y y (memInf (U := ⊤) trivial hi)
    rw [map_zero]
    exact h0
  refine H0.ext_germ fun z hz => ?_
  obtain ⟨j, hj⟩ := hc z
  refine ⟨j, hj, ?_⟩
  have hj0 : f.loc j = 0 := by
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (B.U i).isOpen (B.U j).isOpen ⟨y, hi⟩ ⟨z, hj⟩
    apply germ_injective_of_isIntegral Y w (memInf (U := ⊤) trivial hwj)
    rw [map_zero]
    have e := H0.germ_change (O := ⊤) i j w (show w ∈ (⊤ : Y.Opens) from trivial) hwi hwj f
    have e2 : H0.germ (O := ⊤) i w (show w ∈ (⊤ : Y.Opens) from trivial) hwi f = 0 := by
      rw [H0.germ_apply, hi0, map_zero]
    rw [e2] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  rw [H0.germ_apply, hj0, map_zero, map_zero]

theorem mul_ne_zero : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {P B N : LB Y} (C : ProdChart P B N) (σ : H0 p P ⊤) (f : H0 p B ⊤), σ ≠ 0 → f ≠ 0 → C.mul σ f ≠ 0 := by
  intro k _ Y _ p P B N C σ f hσ hf hmul
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  have e := C.germ_mul σ f t y trivial ha hb hc
  rw [hmul, map_zero] at e
  rcases mul_eq_zero.mp e.symm with h | h
  · exact hσ (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.a t, h.1⟩) σ y _ ha h)
  · exact hf (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.b t, h.2.1⟩) f y _ hb h)

end GlobalTheory.Vanishing.ProdNe
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowth

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (X := (Y₀ X Z))) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowthStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

theorem _root_.GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) → letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) → ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  first | exact @GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | exact GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | (intros; apply GlobalTheory.NefCuspGrowth.topSelf_le_growthOn <;> assumption)
end
end
