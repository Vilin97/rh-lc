module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBoxStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineHodgeTateMultiplicityNeZeroOfJump

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hc : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil a).restrictScalars Qp).subtype).comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil (a + 1)).restrictScalars Qp).subtype := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    rfl
  exact ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y,
    LinearMap.congr_fun hc y⟩

theorem fildR_succ_le (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_DdR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a ≤ DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero_of_jump (ρ : Representation LL G V) [Module.Finite LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : multV PD ρ τ a ≠ 0 := by
  intro h0
  apply h
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_DdR PD ρ τ a)
  refine Submodule.eq_of_le_of_finrank_eq (fildR_succ_le PD ρ τ a) ?_
  unfold multV at h0
  omega

end General

theorem jump_multV_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL),
    Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  intro l _ P K LL T hF τ u hJ
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hfin, -⟩, -⟩ := hF ↥LL.1 ↥(OL LL) (GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL) A
  haveI : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) := hfin
  exact multV_ne_zero_of_jump (P.PD K) T.ρ τ u hJ

end GlobalTheory.HTW.Rec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineHodgeTateMultiplicityNeZeroOfJumpStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL), Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  first | exact @GlobalTheory.HTW.Rec.jump_multV_ne_zero | exact GlobalTheory.HTW.Rec.jump_multV_ne_zero | (intros; apply GlobalTheory.HTW.Rec.jump_multV_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentatStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumps

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumpsStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  first | exact @GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | exact GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | (intros; apply GlobalTheory.HTW.Rec.fits_lowCount_of_matRep <;> assumption)
end
end
