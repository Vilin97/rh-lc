module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSection

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreChartPointMumfordMultiplierNonz

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumMult.exists_pt_chart_of_leadPt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i')), GlobalTheory.MumMult.LeadPt U b m → ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ GlobalTheory.MumMult.multW U b 0 i i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  intro R _ _ _ D A G _ _ U b m hL
  obtain ⟨x, hx, H⟩ := hL

  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1))))
  have hp : (thick R (maximalIdeal R) 0) p = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) p.asIdeal = maximalIdeal R
    refine ((maximalIdeal.isMaximal R).eq_of_le (p.isPrime.comap _).ne_top ?_).symm
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hr)]
    exact p.asIdeal.zero_mem
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom)
    (g := thick R (maximalIdeal R) 0) x p (hx.trans hp.symm)
  obtain ⟨y, hy⟩ := (U.gt 0).q_surj.surj z
  refine ⟨y, ?_, ?_⟩
  · have hc := U.LG.isLB.cover
    have hmem : (fstG (maximalIdeal R) 0 G).left y ∈ (⨆ j, U.LG.L.U j) := by rw [hc]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact ⟨fun _ => j, Set.mem_iInter.2 fun _ => hj⟩
  · intro i i' hy'
    refine H y ?_ i i' hy'
    show (D.toPre.prBe (maximalIdeal R) 0).left ((U.gt 0).q.left y) = x
    rw [hy]
    exact hz
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreChartPointMumfordMultiplierNonzStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_closedFibre_chart_point_mumfordMultiplier_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i')), GlobalTheory.MumMult.LeadPt U b m → ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ GlobalTheory.MumMult.multW U b 0 i i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  first | exact @GlobalTheory.MumMult.exists_pt_chart_of_leadPt | exact GlobalTheory.MumMult.exists_pt_chart_of_leadPt | (intros; apply GlobalTheory.MumMult.exists_pt_chart_of_leadPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaExpansionOfSectionPowerGeThre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecExp

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_restrict' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ f : IntFam (maximalIdeal R) D.toPre k, ∀ e : ℕ, U.ExpandsAt e k s f.f := by
  intro R _ _ _ hB D A G _ _ hG U k hk s
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  obtain ⟨sK, hsK⟩ := exists_restrict' U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
    (pullback.fst G.hom (jK R)) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) s
  obtain ⟨E, hE, -⟩ := (U.expand k (by omega)).1 sK
  obtain ⟨g, hg, hext⟩ := GlobalTheory.IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k s sK hsK E hE
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold scal; rw [map_one, map_one]
  refine ⟨⟨E, g, fun α => h1 ▸ hext α, fun e => ?_⟩, hg⟩
  obtain ⟨S, hS, -⟩ := hg e
  refine S.finite_toSet.subset fun α hα => by_contra fun h => hα fun j => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  apply ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (U.gt e).q.left
  rw [map_zero]
  have h' := hS α h j
  have e' : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  rw [e', Scheme.Hom.comp_app] at h'
  exact h'

end GlobalTheory.Mum.SecExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaExpansionOfSectionPowerGeThreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_integralThetaExpansion_of_section_power_ge_three : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ f : IntFam (maximalIdeal R) D.toPre k, ∀ e : ℕ, U.ExpandsAt e k s f.f := by
  first | exact @GlobalTheory.Mum.SecExp.exists_intFam | exact GlobalTheory.Mum.SecExp.exists_intFam | (intros; apply GlobalTheory.Mum.SecExp.exists_intFam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.MumMult

theorem exists_closedFibre_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) :
    ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
  let y : (𝟙_ (Over (Sp R))).left := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  refine ⟨(η[D.toPre.P.A]).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w (η[D.toPre.P.A])]
  rfl

theorem exists_N_sec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  intro R _ _ _ hR D a a' h h' hE
  have := D.toPre.P.isAb.proper
  have hP := D.toPre.P.isLB
  obtain ⟨N₀, hN₀, -, hκ⟩ := GlobalTheory.Mum.PosMult.exists_pos_mult R hR.1 D a a' h h' hE
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.Mum.PosMult.eventually_relAmple R D.toPre.P a
  have hA : IsAmpleLB D.toPre.P.L := isAmpleLB_of_relAmple_of_isAffine D.toPre.P.A hP D.toPre.P.ample
  have hNb := LB.isLB_linComb hP (K := Fin 1) ![a.left] ![1]
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (GlobalTheory.AmpleDominates.eventually_isGenerated D.toPre.P.A.hom hA hNb)
  set N := max N₀ (max N₁ N₂) with hNdef
  have hN0 : N₀ ≤ N := le_max_left _ _
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hL' := LB.isLB_linComb hP (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]
  have hG := hN₂ N hN2
  have hD := LB.isLB_div (isLB_lbPow hP N) hNb
  have hGen : IsGenerated (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) := by
    refine hG.of_lbIso hL' ((cls_eq_iff hL' hD).1 ?_)
    rw [cls_linComb hP, cls_div (isLB_lbPow hP N) hNb, cls_lbPow hP, cls_linComb hP]
    simp [Fin.sum_univ_two, GlobalTheory.CechPic.pull_id]
    abel
  refine ⟨N, le_trans hN₀ hN0, ⟨hN₁ N hN1, ?_⟩, ?_⟩
  · intro κ hs h0 hc hint hb y
    obtain ⟨r, hr⟩ := hκ κ hs h0 hc hint hb y
    obtain ⟨r', hr'⟩ := hint y
    refine ⟨r' ^ (N - N₀) * r, ?_⟩
    have hsplit : (κ y : FractionRing R) ^ N = (κ y : FractionRing R) ^ (N - N₀) * (κ y : FractionRing R) ^ N₀ := by
      rw [← pow_add, Nat.sub_add_cancel hN0]
    have hr0 : ((κ y ^ N₀ : (FractionRing R)ˣ) : FractionRing R) = (κ y : FractionRing R) ^ N₀ := Units.val_pow_eq_pow_val _ _
    rw [Units.val_pow_eq_pow_val, hsplit, ← hr0, hr, map_mul, map_pow, ← hr']
    ring
  · obtain ⟨x, hx⟩ := exists_closedFibre_pt R D
    obtain ⟨σ₀, hσ⟩ := hGen.exists_mem x
    refine ⟨σ₀, x, hx, fun j hj => ?_⟩
    exact (mem_nonzeroLocus_iff_basicOpen σ₀ hj).1 hσ

end GlobalTheory.MumMult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_exponent_nonzero_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  first | exact @GlobalTheory.MumMult.exists_N_sec | exact GlobalTheory.MumMult.exists_N_sec | (intros; apply GlobalTheory.MumMult.exists_N_sec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_of_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  first | exact @GlobalTheory.MumMult.exists_mult_of_posN | exact GlobalTheory.MumMult.exists_mult_of_posN | (intros; apply GlobalTheory.MumMult.exists_mult_of_posN <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordMultiplierThickeningChartSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumMult

theorem chart_main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')), (∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), GlobalTheory.MumMult.ChartExpOn U.toUnifPre e (N * k) i' (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ (((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, hpos, σ₀, x, hx, hσ⟩ := GlobalTheory.T.exists_mumfordMultiplier_exponent_nonzero_section R hB D a a' h h' hE
  obtain ⟨m, hAct, hLead⟩ := GlobalTheory.T.exists_mumfordMultiplier_of_section R hB D A G hG U a a' h h' hE b hb N hN hpos σ₀ x hx hσ
  refine ⟨N, hN, m, fun k hk s => ?_, GlobalTheory.T.exists_closedFibre_chart_point_mumfordMultiplier_nonzero R D A G U b m hLead⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_integralThetaExpansion_of_section_power_ge_three R hB D A G hG U k hk s
  exact hAct k hk f s hf

end GlobalTheory.MumMult
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordMultiplierThickeningChartSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mumfordMultiplier_thickening_chart_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')), (∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), GlobalTheory.MumMult.ChartExpOn U.toUnifPre e (N * k) i' (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ (((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  first | exact @GlobalTheory.MumMult.chart_main | exact GlobalTheory.MumMult.chart_main | (intros; apply GlobalTheory.MumMult.chart_main <;> assumption)
end
end
