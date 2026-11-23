module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGeneratorCharTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKerStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphicStatement
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BiKill

open GlobalTheory.CechPic

theorem lam_lam_diag {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (a b : T ⟶ A) :
    lam (lam (cls M hM) (𝟙 A) (𝟙 A)) a b = 2 • lam (cls M hM) a b := by
  have e : ∀ h : T ⟶ A, pull h.left (lam (cls M hM) (𝟙 A) (𝟙 A)) = lam (cls M hM) h h := fun h =>
    by rw [pull_lam, Category.comp_id]
  have hr : ∀ x y z : T ⟶ A, lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [lam_comm, lam_mul_left hM hΘ, lam_comm _ y, lam_comm _ z]
  change pull (a * b).left _ - pull a.left _ - pull b.left _ + pull (1 : T ⟶ A).left _ = _
  rw [e, e, e, e, lam_mul_left hM hΘ, hr, hr, lam_one_left, lam_comm _ b a, two_smul]
  abel

theorem kernel_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  intro A _ _ g hA hg P hP h1 h2 hsw hamp n hn T x hx
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsw
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ A hA M hM
  have hcube : (cubeLB A ![fst A A, snd A A] M).IsLB := LB.isLB_linComb hM _ _
  have hcP : cls P hP = lam (cls M hM) (fst A A) (snd A A) :=
    ((cls_eq_iff hP hcube).2 hPM).trans (cls_cube_two hM _ _ hcube)
  have hpullP : ∀ {Y : Over (Sp ℂ)} (a b : Y ⟶ A) (h : (P.pull (lift a b).left).IsLB),
      cls _ h = lam (cls M hM) a b := by
    intro Y a b h
    rw [cls_pull hP, hcP, pull_lam, lift_fst, lift_snd]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hcL : cls _ hL = lam (cls M hM) (𝟙 A) (𝟙 A) := hpullP _ _ hL
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨u, Hm, χ, -, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  obtain ⟨Q, ψ, ρ, N, hN, hψ, hρ, e₁, e₂, e₃⟩ :=
    GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL hAH
  have hlamM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hlamL : (abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).IsLB := LB.isLB_linComb hL _ _
  have hker : ∀ {Y : Over (Sp ℂ)} (y : Y ⟶ A),
      (∃ t : (P.pull (lift (snd A Y ≫ y) (fst A Y)).left).Gen, t.IsGen) →
      GlobalTheory.RealMult.HasGen ((abelian₂ A M).pull (lift (fst A Y) (snd A Y ≫ y)).left) ∧
      GlobalTheory.RealMult.HasGen ((abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).pull (lift (fst A Y) (snd A Y ≫ y)).left) := by
    intro Y y ht
    have h0 : lam (cls M hM) (fst A Y) (snd A Y ≫ y) = 0 := by
      rw [lam_comm, ← hpullP _ _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).2 ht
    refine ⟨(cls_eq_zero_iff (pull_isLB hlamM _)).1 ?_, (cls_eq_zero_iff (pull_isLB hlamL _)).1 ?_⟩
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hM]
      exact h0
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hL, hcL, lam_lam_diag hM hΘ, h0, smul_zero]
  have hk : x ^ (N * N) = 1 :=
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL Q ψ ρ N hψ hρ e₁ e₂ e₃ T x (hker x hx).2
  have key := GlobalTheory.torsion_point_comp_eq_one A hA M ((𝟙 A) ^ n) (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_)
    T x hk (hker x hx).1
  · rwa [MonObj.comp_pow, Category.comp_id] at key
  · rw [MonObj.comp_pow, Category.comp_id]
    refine hn y ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    rw [hpullP, lam_comm, ← GlobalTheory.RealMult.Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamM _)]
    exact (cls_eq_zero_iff _).2 hy

end GlobalTheory.BiKill
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  first | exact @GlobalTheory.BiKill.kernel_pow_eq_one | exact GlobalTheory.BiKill.kernel_pow_eq_one | (intros; apply GlobalTheory.BiKill.kernel_pow_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HalvedPeriod

open GlobalTheory.CechPic GlobalTheory.Models GlobalTheory.ZM

theorem exists_abelian_of_isPeriod : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  intro O _ bar g ρ D' Q E₁ hP hE
  obtain ⟨hlin, -, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ Q.range := fun z => Iff.rfl
  have hΛd : DiscreteTopology Λ := hdisc
  have hΛs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have e : (Λ : Set (Fin g → ℂ)) = Set.range Q := by
      ext z; exact AddMonoidHom.mem_range
    rw [e]; exact hspan
  let H₁ : Matrix (Fin g) (Fin g) ℂ := (2⁻¹ : ℂ) • Hm
  have hH₁ : H₁.IsHermitian := by
    unfold Matrix.IsHermitian at hHm ⊢
    simp only [H₁, Matrix.conjTranspose_smul, hHm, star_inv₀, star_ofNat]
  have hH₁v : ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁ *ᵥ star w = 2⁻¹ * hermForm Hm z w := fun z w => by
    simp only [H₁, hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH₁pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁ *ᵥ star z).re := fun z hz => by
    rw [hH₁v]
    have := hpos z hz
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.re_ofReal_mul]
    positivity
  have hH₁int : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ H₁ *ᵥ star l').im = n := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨E₁ x y, ?_⟩
    have h := him x y
    rw [hE] at h
    rw [hH₁v]
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.im_ofReal_mul, h]
    simp
  obtain ⟨A, _, hA, hdim, M, u, χ, hM, hu, hAH⟩ :=
    GlobalTheory.riemann_polarised_torus g Λ H₁ hΛd hΛs hH₁ hH₁pos hH₁int
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ Q.range := fun z => (u.ker z).trans (hu z)
  obtain ⟨u', χ', hex, hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u H₁ χ hM
    (GlobalTheory.TorusRM.isFactorAH_of_isAH hAH)
  have h2H : (2 : ℂ) • H₁ = Hm := by simp only [H₁, smul_smul]; norm_num
  rw [h2H] at hF'
  have hAH' : u'.IsAH Hm χ' := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' (fun z hz => hpos z hz)
  have hker' : ∀ z, z ∈ u'.Λ ↔ z ∈ Q.range := fun z => by rw [← u'.ker, hex, hker]
  have hPLB := GlobalTheory.FullSiegel.isLB_lam hM
  have hΔLB := pull_isLB hPLB (lift (𝟙 A) (𝟙 A)).left

  have hid : IsGrpPullback A A (𝟙 _) (𝟙 A.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))
  have htb := GlobalTheory.TorusTransfer.tangent_bijective u hdim
  have hexp : IsExp (𝟙 (Sp ℂ)) u.ex :=
    GlobalTheory.PointUnif.isExp_push hid u htb.1 htb.2 (MulEquiv.refl _) (fun x => (Category.comp_id _).symm)

  have hρΛ : ∀ a, ∀ x ∈ u.Λ, Matrix.mulVecLin (ρ a) x ∈ u.Λ := by
    intro a x hx
    rw [hu, hmem] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [Matrix.mulVecLin_apply, hlin]⟩
  choose ψ hψ hlift using fun a =>
    GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA hdim M u (Matrix.mulVecLin (ρ a)) (hρΛ a)
  haveI : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hA.smooth
  have hext : ∀ f f' : A ⟶ A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  let act : OActN O A :=
    { act := ψ
      hom := hψ
      one := hext _ _ fun z => by
        rw [← hlift, map_one, Matrix.mulVecLin_one, LinearMap.id_apply, Category.comp_id]
      mul := fun a b => hext _ _ fun z => by
        rw [← hlift, ← Category.assoc, ← hlift, ← hlift]
        congr 1
        simp only [Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
      add := fun a b => hext _ _ fun z => by
        rw [← hlift, comp_mul, ← hlift, ← hlift, ← u.ex_add]
        congr 1
        simp [Matrix.add_mulVec] }
  refine ⟨A, inferInstance, inferInstance, act, abelian₂ A M, u.ex, hA, hdim, hPLB, ?_, ?_, GlobalTheory.FullSiegel.lam_symm hM,
    GlobalTheory.LefschetzAmple.relAmple_of_isAH g A hA _ u' Hm χ' hΔLB hAH', hexp, hker, fun a z => ?_, ?_⟩
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_left _ _))
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_right _ _))
  · rw [← Matrix.mulVecLin_apply]; exact hlift a z
  · intro k a b c hk hc
    have h := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hΔLB g u' Hm χ' hAH' k (Q a) (Q b) c hk
      ((hker' _).2 ⟨a, rfl⟩) ((hker' _).2 ⟨b, rfl⟩) (by
        rw [hc]
        have e : (Q a ⬝ᵥ Hm *ᵥ star (Q b)).im = (D'.EF a b : ℝ) := him a b
        rw [e]; push_cast; rfl)
    rw [hex] at h
    exact h

end GlobalTheory.HalvedPeriod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_abelianVariety_of_halved_periodMap : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  first | exact @GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | exact GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | (intros; apply GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Build

lemma exp_nsmul {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (z : Fin g → ℂ) : ∀ n : ℕ, e (n • z) = e z ^ n := by
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

lemma exists_nsmul_eq_of_dvd {La : Type} [AddCommGroup La] (EF E₁ : LinearMap.BilinForm ℤ La) (hE₁ : EF = (2:ℤ) • E₁)
    (e₀ : ℕ) (a : La) (k : ℕ) (hdv : ∀ y, (k : ℤ) ∣ E₁ a y) (nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0)
    (hperf : ∀ f : La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e₀ • f) : ∃ x', e₀ • a = k • x' := by
  let φ : La →ₗ[ℤ] ℤ :=
    { toFun := fun y => E₁ a y / k
      map_add' := fun u v => by
        rw [map_add (f := _)]; exact Int.add_ediv_of_dvd_left (hdv u)
      map_smul' := fun c u => by
        rw [map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdv u) }
  obtain ⟨x', hx''⟩ := hperf φ
  refine ⟨x', ?_⟩
  rw [← sub_eq_zero]
  apply nondeg
  intro y
  have hφ : E₁ x' y = e₀ * (E₁ a y / k) := by
    have := congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''
    simpa [φ] using this
  have hm : (k : ℤ) * (E₁ a y / k) = E₁ a y := Int.mul_ediv_cancel' (hdv y)
  rw [hE₁]
  simp only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]
  linear_combination (-2 * (e₀:ℤ)) * hm

lemma half_unique {La : Type} [AddCommGroup La] (E E' : LinearMap.BilinForm ℤ La) (h : (2:ℤ) • E = (2:ℤ) • E') :
    E = E' := by
  ext u v
  have h2 := congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h
  simp only [LinearMap.smul_apply, smul_eq_mul] at h2
  omega

end GlobalTheory.UPel.HT.Build


open GlobalTheory.UPel.HT.Build in
theorem GlobalTheory.UPel.HT.exists_obj_unifAt_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper
  obtain ⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩ := hcls
  obtain ⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩ :=
    GlobalTheory.T.exists_abelianVariety_of_halved_periodMap D.O D.inv D.g ρ D' Q E₁ hper hE₁
  have hadd := hexp.1
  have hsurj := hexp.2.1
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.lieCondition_of_complexExp_intertwines_action p D R b N σ ρ A act e hab hdim hexp hact htype
  have hgen' := hgen
  obtain ⟨f, ν, rfl, -, hf⟩ := hgen
  have hfN := hf N hN hNp
  let eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun a => e ((N : ℂ)⁻¹ • Q (f N a))
  have heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a)) := fun a => Category.id_comp _
  have hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c := by
    intro c k x
    rw [hper.1, ← Matrix.mulVec_smul, hact]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ1 : ∀ x, e (Q x) = 1 := fun x => (hker _).2 ⟨x, rfl⟩
  have hgeom := GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker
    hact hweil heta
  let o : Obj b N (spMap σ) :=
    { A := A
      ab := hab
      act := act
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := hsy
      ample := ham
      kerP := ⟨e₀, he₀p, GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by
        obtain ⟨k, hk, hxk⟩ := GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1
          hper.2.2.2.1 hker hweil x hx
        obtain ⟨z, rfl⟩ := hsurj x
        have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have h1 : e (k • z) = 1 := by rw [exp_nsmul e hadd]; exact hxk
        obtain ⟨a, ha⟩ := (hker _).1 h1
        have hz : z = (k : ℂ)⁻¹ • Q a := by
          rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]
        obtain ⟨E₁', hE₁', hdiv⟩ := GlobalTheory.T.diag_form_two_smul_and_ker_alt A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp
          hper.2.1 hker hweil
        have hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a))
            (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen := by
          rw [← hz]; exact hx
        have hdv : ∀ y, (k : ℤ) ∣ E₁' a y := (hdiv k a hk).2 hx'
        have hEE : E₁' = E₁ := half_unique _ _ (hE₁'.symm.trans hE₁)
        rw [hEE] at hdv
        obtain ⟨x', key⟩ := exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf
        have hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a) := by
          rw [smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk',
            one_smul]
        show e z ^ e₀ = 1
        rw [← exp_nsmul e hadd, hz, ← hQ]
        exact hQ1 x')⟩
      rosati := fun c => by
        refine (GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil
          (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c))
          (AddMonoidHom.mk' (fun x => (D.star c).unop • x) (smul_add _)) (act.hom c) (act.hom _)
          (fun k x _ => hsc c _ x) (fun k x _ => hsc _ _ x)).2 ?_
        intro x y
        exact D'.adj c x y
      lie := hlie
      lieRank := fun k _ _ x β hx i => hlieR k x β hx i
      eta := eta
      eta_add := fun x y => by
        show e _ = e _ * e _
        erw [map_add (f N) x y, map_add, smul_add, hadd]
        rfl
      eta_lin := fun c x => by
        obtain ⟨e', he'⟩ := hfN.2.1 c x
        show e _ = e _ ≫ _
        erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]
      eta_ker := fun x => by
        show e _ = 1
        erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]
      geom := fun k _ _ x β _ => hgeom k x }
  refine ⟨o, hdim, pull_isLB hP _, e, ?_⟩
  refine ⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩
end
end
