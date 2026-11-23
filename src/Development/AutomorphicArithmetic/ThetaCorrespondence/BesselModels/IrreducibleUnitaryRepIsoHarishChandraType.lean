module

public import Formalism.PeriodIntegrals.UpqRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsWtOnIffOfTorus
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HWSpan
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.EqSmulOfWeight
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarishChandraParameters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightsCompactStabilizer

section

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b = (if b = c then E a d else (0 : A)) - if d = a then E c b else (0 : A)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit :
    {n : ℕ} →
      {V : Type} →
        [inst : NormedAddCommGroup V] →
          [inst_1 : InnerProductSpace ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Prop :=
    fun {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
        (E : Fin n → Fin n → Module.End ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ (x y : V), Inner.inner ℂ ((E a b : V → V) x) y = Inner.inner ℂ x ((E b a : V → V) y)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Submodule ℂ V → Prop :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
        (S : Submodule ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ v ∈ S, (E a b : V → V) v ∈ S

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight.{u_1} :
    {V : Type u_1} →
      [inst : AddCommGroup V] →
        [inst_1 : _root_.Module ℂ V] → {n : ℕ} → (Fin n → Fin n → Module.End ℂ V) → (Fin n → ℝ) → V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ)
        (w : V) ↦
      ∀ (a : Fin n), (E a a : V → V) w = (↑(μ a) : ℂ) • w

theorem UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight :
    ∀ {n : ℕ} {ε : Fin n → Bool} {V : Type} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℂ V]
      {E : Fin n → Fin n → Module.End ℂ V},
      UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel E →
        UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit ε E →
          ∀ {Q : Submodule ℂ V} [FiniteDimensional ℂ ↥Q],
            UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab ε E Q → Q ≠ ⊥ → ∃ (ν : Fin n → ℝ), ∃ x ∈ Q, x ≠ (0 : V) ∧ UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight E ν x := by
  intro n ε V _ _ E hG hU Q _ hS hQ
  classical
  let T : Fin n → Module.End ℂ Q := fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)
  have hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x := fun a x => rfl
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT]
    exact hU a a rfl x y
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a b hab
    have h := hG a a b b
    rw [if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero] at h
    change T a * T b = T b * T a
    ext x
    have := congrArg (fun f : Module.End ℂ V => f x) h
    simpa [hT] using this
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact bot_ne_top htop
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a) := fun a =>
    (Submodule.mem_iInf _).mp hx a
  have hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a := fun a =>
    Complex.conj_eq_iff_re.mp
      ((hsym a).conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))
  refine ⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩
  have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))
  rw [hT] at h
  rw [hre a, h]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.KShift

section

@[expose] public section

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
open GlobalTheory.CompanionTheory.KLowSpan (kLowSpan KLower)
open PI.UpqRep (root)

noncomputable section

namespace UpperTheory.Lit.Bur.KShift

variable {n : ℕ} {ε : Fin n → Bool}

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}

theorem kUnit_of (hU : IsUnitary ε E) : KUnit ε E := by
  intro a b hab y z
  have := hU a b y z
  simpa [Formalism.REAL.sgn, hab] using this

theorem exists_weight (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ ν : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x :=
  _root_.UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight hE hU hQ hQ0

theorem exists_highest (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ μ : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ KHighest ε E μ x := by
  classical
  let ht : (Fin n → ℝ) → ℝ := fun ν => ∑ c : Fin n, ((c : ℕ) : ℝ) * ν c
  let h : Module.End ℂ V := ∑ c : Fin n, (((c : ℕ) : ℝ) : ℂ) • E c c
  have hhQ : ∀ w ∈ Q, h w ∈ Q := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Q.sum_mem fun c _ => Q.smul_mem _ (hQ c c rfl w hw)
  have hh : ∀ (ν : Fin n → ℝ) (x : V), IsWeight E ν x → h x = ((ht ν : ℝ) : ℂ) • x := by
    intro ν x hx
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hx _, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℝ := {t | ∃ ν : Fin n → ℝ, ht ν = t ∧ ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhQ)
    refine (hfin.preimage (f := fun t : ℝ => (t : ℂ)) Complex.ofReal_injective.injOn).subset ?_
    rintro t ⟨ν, rfl, x, hxQ, hx0, hx⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxQ⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh ν x hx)
    · exact fun h0 => hx0 (congrArg Subtype.val h0)
  obtain ⟨ν₀, x₀, hx₀Q, hx₀, hx₀w⟩ := exists_weight hE hU hQ hQ0
  have hSne : S.Nonempty := ⟨_, ν₀, rfl, x₀, hx₀Q, hx₀, hx₀w⟩
  obtain ⟨t, ⟨ν, rfl, x, hxQ, hx0, hx⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨ν, x, hxQ, hx0, hx, fun a b hab he => ?_⟩
  by_contra hne
  have hmem : ht (ν + root a b) ∈ S :=
    ⟨_, rfl, E a b x, hQ a b he x hxQ, hne, GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hx a b⟩
  have h1 : ht (ν + root a b) = ht ν + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [GlobalTheory.CompanionTheory.DSHighestOfKType.height_root]
  have h2 := hmin _ hmem
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [id] at h2
  linarith

end Alg

section Rep

open CompanionTheory.D.DSIC (IsSmMod hStabLink hWtLink hLowSpan hHWofType hSmMod)
open PI.UpqRep (IsKTypeOf IsKStableOn IsURepOn UJset)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Sm : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ Sm}

end Rep


end UpperTheory.Lit.Bur.KShift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IrreducibleUnitaryRepIsoHarishChandraType

section

@[expose] public section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType

theorem exists_hcType_of_irred : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  intro k Wp _ _ _ _ ρ hρ hirr
  obtain ⟨E, hgl, hun, hE⟩ := Derived.exists_derived_action k Wp ρ hρ
  have hQ : CompanionTheory.D.DSIC.KStab (PI.UpqRep.allPos k) E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ _ => trivial
  obtain ⟨μ, x, -, hx0, hx⟩ := UpperTheory.Lit.Bur.KShift.exists_highest hgl (UpperTheory.Lit.Bur.KShift.kUnit_of hun) hQ top_ne_bot
  have hlow : PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k) = μ := by
    rw [GlobalTheory.KTypeCompare.lowK_allPos]
    simp
  have hΛ : Formalism.REAL.KHighest (PI.UpqRep.allPos k) E
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k)) x := by
    rw [hlow]; exact hx
  have htype := exists_type_of_highest hρ E hgl hun hE _ x hx0 hΛ
  set S := Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x with hS
  have hst := Wt.stable_of_derived hρ E hE S (Formalism.REAL.isCompactInvariant_compactSpan x)
  have hxS : x ∈ S := Formalism.REAL.mem_compactSpan x
  have htop : S = ⊤ := (hirr S hst).resolve_left fun h => hx0 (by
    rw [h] at hxS; exact (Submodule.mem_bot ℂ).1 hxS)
  refine ⟨_, S, inferInstance, inferInstance, compress ρ S, (LinearEquiv.ofTop S htop).symm, htype, ?_⟩
  intro h hh w
  apply Subtype.ext
  rw [coe_compress (hst h hh _ (Subtype.property _))]
  simp [LinearEquiv.ofTop_symm_apply]

end UpperTheory.Lit.Bur.HWSpanType

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  first | exact @UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | exact UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | (intros; apply UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred <;> assumption)
end
end
end
