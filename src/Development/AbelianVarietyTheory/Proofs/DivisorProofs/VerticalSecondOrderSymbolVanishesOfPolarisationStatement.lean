module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShiftedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSections

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleCover

variable {X : Scheme.{0}} (U : X.Opens) (hU : U = ⊤)

noncomputable def backTop : X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (𝟙 X) (by
    rw [Scheme.Opens.range_ι, hU]; exact Set.subset_univ _)

theorem backTop_ι : backTop U hU ≫ U.ι = 𝟙 X := IsOpenImmersion.lift_fac _ _ _

theorem backTop_apply (y : X) : U.ι (backTop U hU y) = y :=
  congrArg (fun g : X ⟶ X => g y) (backTop_ι U hU)

instance : IsIso (backTop U hU) :=
  ⟨⟨U.ι, backTop_ι U hU, by rw [← cancel_mono U.ι, Category.assoc, backTop_ι, Category.comp_id, Category.id_comp]⟩⟩

end GlobalTheory.AmpleCover

namespace GlobalTheory.AmpleCover

variable {S : Scheme.{0}} (A : Over S) (L : LB A.left) (N : ℕ)

theorem gm_pow_congr {y : A.left} {r : A.left ⟶ A.left} (hr : r = 𝟙 A.left) (a b : L.ι) :
    gm (𝟙 A.left) y (L.U a ⊓ L.U b) (L.g a b) ^ N = gm r y (L.U a ⊓ L.U b) (L.g a b) ^ N := by
  subst hr; rfl

def chartPullPowTop :
    ChartPull (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 A.left) fun _ => (N : ℤ)) (powOver A L ⊤ N)
      (backTop (A.hom ⁻¹ᵁ ⊤) (by simp)) where
  idx j := fun _ => (j : Fin 1 → L.ι) 0
  le j y hy := Set.mem_iInter.2 fun _ => by
    have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
    have hy' : y ∈ L.U ((j : Fin 1 → L.ι) 0) := Set.mem_iInter.1 hy 0
    show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U ((j : Fin 1 → L.ι) 0)
    rw [e]; exact hy'
  g y j j' hj hj' := by
    have hb : ∀ (i : Fin 1 → L.ι), y ∈ L.U (i 0) →
        backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y ∈ (powOver A L ⊤ N).U (fun _ => i 0) := fun i hi =>
      Set.mem_iInter.2 fun _ => by
        have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
        show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U (i 0)
        rw [e]; exact hi
    refine (gm_linComb L _ _ (𝟙 _) y j j' hj hj').trans (Eq.trans ?_
      (gm_linComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) _ y _ _
        (hb j (Set.mem_iInter.1 hj 0)) (hb j' (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fintype.prod_unique]
    simp only [backTop_ι, Category.id_comp, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      zpow_natCast]
    exact gm_pow_congr A L N (backTop_ι _ _) _ _

end GlobalTheory.AmpleCover


open GlobalTheory.AmpleCover in
theorem GlobalTheory.AmpleCover.exists_affine_cover_secM : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  intro K _ P₀
  obtain ⟨N, hN, M, s, hcov, hs⟩ := P₀.ample ⊤ (isAffineOpen_top _)
  have hT : P₀.A.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  let a := chartPullPowTop P₀.A P₀.L N
  have loc : ∀ i, Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) = backTop _ hT ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.nonzeroLocus_chartSec a (s i) fun y j hj => by
      have h0 : (P₀.A.hom ⁻¹ᵁ ⊤).ι (backTop _ hT y) ∈ P₀.L.U ((j : Fin N → P₀.L.ι) ⟨0, hN⟩) :=
        Set.mem_iInter.1 hj ⟨0, hN⟩
      rw [backTop_apply] at h0
      exact ⟨fun _ => (j : Fin N → P₀.L.ι) ⟨0, hN⟩, Set.mem_iInter.2 fun _ => h0⟩
  refine ⟨N, {i : Fin (M + 1) // ((Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty},
    fun i => GlobalTheory.chartSec a (s i.1), hN, ?_, fun i => ⟨?_, i.2⟩⟩
  · refine eq_top_iff.2 fun y _ => ?_
    have hy : backTop _ hT y ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    have hy' : y ∈ Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) := by rw [loc]; exact hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, y, hy'⟩, hy'⟩
  · show IsAffineOpen (Out.nonzeroLocus (GlobalTheory.chartSec a (s i.1)))
    rw [loc]
    exact (hs i.1).1.preimage _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSectionsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_cover_by_polarization_power_sections : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  first | exact @GlobalTheory.AmpleCover.exists_affine_cover_secM | exact GlobalTheory.AmpleCover.exists_affine_cover_secM | (intros; apply GlobalTheory.AmpleCover.exists_affine_cover_secM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVariety

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVarietyStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  first | exact @GlobalTheory.HeatConst.const_of_regular_on_cover | exact GlobalTheory.HeatConst.const_of_regular_on_cover | (intros; apply GlobalTheory.HeatConst.const_of_regular_on_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisation

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Heat.gc_symbol_vanishes : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  intro K _ _ P₀ n v dd hv F _ ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hΛ hδ₀ hbr
  obtain ⟨k, I, s, hk, hcov, hai⟩ := GlobalTheory.T.exists_affine_cover_by_polarization_power_sections K P₀
  have haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) := fun i => (hai i).1
  have hne := fun i => (hai i).2
  have hloc : ∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hval _ (hne i)
  have hL := fun i => GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hbr k hk (s i) (hloc i)
  have hreg : ∀ i a e, ∃ h : Γ(P₀.A.left, Out.nonzeroLocus (s i)), valR ξ _ h = Λ a e := fun i =>
    GlobalTheory.T.symbol_entries_regular_affineOpen K P₀ n v dd hv F ψ ξ hξ hval δ hδ Λ _ (haff i) (hloc i) (hL i).1
  have hc : ∀ a e, ∃ r : K, ψ r = Λ a e := fun a e =>
    GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety K P₀ F ψ ξ hξ hval I (fun i => Out.nonzeroLocus (s i)) hcov hloc (Λ a e) (fun i => hreg i a e)
  choose lam hlam using hc
  have hsym : lamᵀ = lam := by
    ext a e
    apply ψ.injective
    show ψ (lam e a) = ψ (lam a e)
    rw [hlam, hlam]
    exact congrFun (congrFun hΛ a) e
  have hks := GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ lam hsym hδ₀ k hk I s hcov haff hloc
    (fun i f => by
      obtain ⟨f', hf'⟩ := (hL i).2 f
      exact ⟨f', by rw [hf']; simp only [hlam]⟩)
  have h0 := GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero K P₀ n v dd hv lam hks
  ext a e
  rw [← hlam a e, h0]
  simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisationStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  first | exact @GlobalTheory.Heat.gc_symbol_vanishes | exact GlobalTheory.Heat.gc_symbol_vanishes | (intros; apply GlobalTheory.Heat.gc_symbol_vanishes <;> assumption)
end
end
