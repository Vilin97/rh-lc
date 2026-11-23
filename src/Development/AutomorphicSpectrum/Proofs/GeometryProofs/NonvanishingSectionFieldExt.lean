module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Mathlib.Tactic.Linter.HaveILetI
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModuleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominatorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrimeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMapStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in
theorem exists_sec_ne_zero_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  intro E _ _ _ H L _ _ D
  have hS : SecBaseChangeAnySt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  obtain ⟨hprop, hamp, hkt⟩ := D.princ
  have eid : spMap (RingHom.id L) = 𝟙 (Sp L) := by
    simp [spMap]
  have hpb : IsPullback (𝟙 D.tK.G.left) D.tK.G.hom D.tK.G.hom (spMap (RingHom.id L)) := by
    rw [eid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : LB.Sec D.tK.PP.L, ¬ ∀ y j, (𝟙 D.tK.G.left : D.tK.G.left ⟶ D.tK.G.left) y ∈ D.tK.PP.L.U j →
      gs (𝟙 D.tK.G.left) y _ (β.f j) = 0 := exists_sec_ne hS
    { A := D.tK.G, g := d, smoothDim := hd, L := D.tK.PP.L, isLB := D.tK.PP.isLB
      ample := hamp
      ktriv := hkt
      isAb := ⟨inferInstance, inferInstance, hprop, ‹_›⟩
      rigid := ⟨D.tK.PP.rig, D.tK.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } (RingHom.id L) hpb
  obtain ⟨w, gw', -⟩ := D.m.lin
  have := D.t.semi.separated
  have := D.t.semi.quasiCompact
  have : CompactSpace D.t.G.left := QuasiCompact.compactSpace_of_compactSpace D.t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (nonZeroDivisors (𝓞 L)) D.m.cart.1 D.t.PP.isLB D.tK.PP.isLB
    ((isGen_iff w).1 gw') β
  obtain ⟨w₁, hw₁⟩ := exists_iso_linComb (F := 𝟙 D.t.G.left) D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  have hM := linComb_isLB D.t.PP.L D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 D.t.G.left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨τ, hτ⟩ := sec_pull_down ((isGen_iff w₁).1 hw₁) D.t.PP.isLB hM σ
  refine ⟨τ, fun h0 => hβ fun y k hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart D.t.PP.isLB (D.m.φ y)
  obtain ⟨k', hk'⟩ := exists_chart hM (D.m.φ y)
  have hz : LB.Sec.f τ k' = 0 := congrArg (fun s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ))) => LB.Sec.f s k') h0
  have e₁ := hτ _ D.m.φ y j k' hj hk'
  rw [hz, gs_zero _ y _ hk', mul_zero, Category.comp_id] at e₁
  have e₂ := hσ y j k hj hk
  rw [e₁, D.m.cart.1.w, cst_comp] at e₂
  have ha' : algebraMap (𝓞 L) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero ha)
  have u₁ : IsUnit (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)) :=
    IsUnit.of_mul_eq_one (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)⁻¹) (by
      rw [← cst_mul, mul_inv_cancel₀ ha', cst_one])
  exact (Units.isUnit _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.exists_nonzero_section_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSet

section

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes

theorem exists_multiple_not_mem :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  intro R _ _ _ M _ _ htf t _ d₀ hd₀ hb V P hP hP0 hV
  by_contra hcon
  push_neg at hcon
  let I : Ideal R :=
    { carrier := {x | ∃ u : M, d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨u, hu⟩
        refine ⟨c • u, ?_⟩
        rw [smul_comm, hu, smul_eq_mul, mul_smul] }
  have hImem : ∀ x, x ∈ I ↔ ∃ u : M, d₀ • u = x • t := fun x => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : d₀ ∈ I := (hImem _).2 ⟨t, rfl⟩
    rw [h] at this
    exact hd₀ (by simpa using this)
  obtain ⟨e, heP, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hle : Ideal.span {e} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 heP
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hcz : ∀ c ∈ C, ∀ z ∈ I, c * z ∈ Ideal.span {e} * I := by
    intro c hc z hz
    obtain ⟨u, hu⟩ := (hImem z).1 hz
    have huV : u ∈ V := hcon z u hu
    have hdiv : ∀ π ∈ P, e ∣ c * π := by
      intro π hπ
      have : π * c ∈ Ideal.span {e} := by
        rw [hC]
        exact Ideal.mul_mem_mul hπ hc
      rw [mul_comm]
      exact Ideal.mem_span_singleton.1 this
    obtain ⟨u', hu'⟩ := hV u huV c e he0 hdiv
    have h1 : (d₀ * e) • u' = (c * z) • t := by
      rw [mul_smul, hu', smul_comm, hu, mul_smul]
    have h2 : d₀ * e ∣ d₀ * (c * z) := hb (c * z) (d₀ * e) u' (mul_ne_zero hd₀ he0) h1
    obtain ⟨w, hw⟩ := (mul_dvd_mul_iff_left hd₀).1 h2
    have h3 : d₀ • u' = w • t := by
      have h4 : e • (d₀ • u' - w • t) = 0 := by
        rw [smul_sub, smul_comm, ← mul_smul e w, ← hw, ← h1, mul_smul, sub_self]
      exact sub_eq_zero.1 (htf e _ he0 h4)
    have hwI : w ∈ I := (hImem w).2 ⟨u', h3⟩
    rw [hw]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hwI
  have hCI : C * I ≤ Ideal.span {e} * I := Ideal.mul_le.2 hcz
  have h5 : Ideal.span {e} * I ≤ Ideal.span {e} * (P * I) := by
    calc Ideal.span {e} * I = P * (C * I) := by rw [hC, mul_assoc]
      _ ≤ P * (Ideal.span {e} * I) := Ideal.mul_mono_right hCI
      _ = Ideal.span {e} * (P * I) := by ring
  have h6 : I ≤ P * I := (Ideal.span_singleton_mul_right_mono he0).1 h5
  have h8 : P * I = ⊤ * I := by
    rw [Ideal.top_mul]
    exact le_antisymm Ideal.mul_le_right h6
  exact hP.ne_top (mul_right_cancel₀ hI0 h8)

end GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSetStatement

section

@[expose] public section

open NumberField


theorem _root_.GlobalTheory.T.exists_section_not_in_set : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | exact GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonvanishingSectionFieldExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

theorem section_and_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Out.H0 D'.t.PP.L 1) (e : Fin D'.g → D'.B.carrier), KeyDeg.NonVan D'.t.G.hom s ∧ LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro E _ _ _ H L _ _ D _
  have : Smooth D.t.G.hom := D.t.semi.smooth
  have : GeometricallyConnected D.t.G.hom := D.t.semi.geomConnected
  have : QuasiCompact D.t.G.hom := D.t.semi.quasiCompact
  have hN : (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))).IsLB :=
    LB.isLB_linComb D.t.PP.isLB _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_nonzero_section_pp_data E H L D
  obtain ⟨d₀, hd₀, hb⟩ := GlobalTheory.T.section_module_bounded_denominator (𝓞 L) D.t.G _ hN t ht
  let I : Ideal (𝓞 L) :=
    { carrier := {x | ∃ u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hI : I ≠ ⊥ := fun h0 => hd₀ (by
    have : d₀ ∈ I := ⟨t, rfl⟩
    rw [h0] at this
    simpa using this)
  obtain ⟨L', _, _, _, y, hy, hB⟩ := GlobalTheory.T.principal_extension_projective_module L D.B.carrier I hI
  obtain ⟨⟨D', m⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
  obtain ⟨hgg, -, io, -, hspan, -⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' m
  obtain ⟨e, he1, he2⟩ := hB D'.B.carrier io hspan hgg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.section_module_field_ext_map E H L D L' D' m
  have : Smooth D'.t.G.hom := D'.t.semi.smooth
  let φ := algebraMap (𝓞 L) (𝓞 L')
  let W : Ideal (𝓞 L') :=
    { carrier := {z | ∃ v : SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), φ d₀ • v = z • P t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hIW : I.map φ ≤ W := Ideal.map_le_iff_le_comap.2 fun x ⟨u, hu⟩ =>
    ⟨P u, by rw [← hP1, hu, hP1]⟩
  obtain ⟨s, hs⟩ : y ∈ W := hIW (hy ▸ Ideal.mem_span_singleton_self y)
  refine ⟨L', inferInstance, inferInstance, inferInstance, D', m, s, e, ?_, he1, he2⟩
  intro b'
  let b : Sp (𝓞 L) := spMap φ b'

  obtain ⟨x, u, hu, yy, hyy, hmem⟩ : ∃ (x : 𝓞 L) (u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))),
      d₀ • u = x • t ∧ ∃ yy : D.t.G.left, D.t.G.hom yy = b ∧ yy ∈ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u := by
    by_cases hb0 : b.asIdeal = ⊥
    · exact ⟨d₀, t, rfl, GlobalTheory.T.nonzero_section_generic_fibre (𝓞 L) D.t.G _ hN t ht b hb0⟩
    · have hmax : b.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hb0 b.isPrime
      obtain ⟨x, u, hu, hV⟩ := GlobalTheory.T.exists_section_not_in_set (𝓞 L) _ (fun a m ha h => eq_zero_of_smul_eq_zero ha h) t ht d₀ hd₀ hb
        {u | ∀ yy : D.t.G.left, D.t.G.hom yy = b → yy ∉ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u}
        b.asIdeal hmax hb0 (fun u hu c e he h => GlobalTheory.T.section_module_divisible_at_prime (𝓞 L) _ D.t.G.hom _ b hmax u hu c e he h)
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hV
      obtain ⟨yy, hyy, hmem⟩ := hV
      exact ⟨x, u, hu, yy, hyy, hmem⟩
  obtain ⟨y', hy', hm'⟩ := hP2 u b' yy hyy hmem
  refine ⟨y', hy', ?_⟩
  have hxI : φ x ∈ I.map φ := Ideal.mem_map_of_mem φ (show x ∈ I from ⟨u, hu⟩)
  rw [hy, Ideal.mem_span_singleton'] at hxI
  obtain ⟨w, hw⟩ := hxI
  have hφ : φ d₀ ≠ 0 := fun h0 => hd₀ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L') (h0.trans (map_zero _).symm))
  have hPu : P u = w • s := by
    have : φ d₀ • (P u - w • s) = 0 := by
      rw [smul_sub, ← hP1, hu, hP1, smul_comm, hs, smul_smul, ← hw, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero hφ this)
  rw [hPu] at hm'
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have : y' ∈ D'.t.G.left.basicOpen (constFn D'.t.G.hom _ w * LB.Sec.f (show SecMod D'.t.G.hom _ from s) k) := hk
  rw [Scheme.basicOpen_mul] at this
  exact this.2

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
end
end
end
