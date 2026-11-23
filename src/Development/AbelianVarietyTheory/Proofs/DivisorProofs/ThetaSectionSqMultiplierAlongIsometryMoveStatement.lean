module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
public import Development.AutomorphicArithmetic.WeightCongruences.DvdNormSubOneOfIdempotentInterpolationRelNormOne
public import Development.AutomorphicArithmetic.WeightCongruences.NormRootOfUnityQuadraticSubfield
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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceW0PowFourEven

section

@[expose] public section

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AdaptedDet

namespace GlobalTheory.AdaptedDetSign

theorem det_interp_gen {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0)
    (e t δ : 𝓞 E) (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = (δ : E)) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((e * δ + (1 - e) + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = algebraMap E K ((e : E) * (δ : E) + (1 - (e : E))) + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h, map_add (f := _), map_mul, map_sub, map_one]
  have hy' : IsIntegral ℤ ((d - ((e : E) * (δ : E) + (1 - (e : E)))) / n) := by
    rw [← isIntegral_algebraMap_iff (B := K), map_div₀, map_sub, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - ((e : E) * (δ : E) + (1 - (e : E)))) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((e * δ + (1 - e) + n * z : 𝓞 E) : E) =
      (e : E) * (δ : E) + (1 - (e : E)) + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring

theorem norm_one_add_two {E : Type} [Field E] [NumberField E] (u : 𝓞 E) :
    (4 : ℤ) ∣ Algebra.norm ℤ (1 + 2 * u : 𝓞 E) - (1 + 2 * Algebra.trace ℤ (𝓞 E) u) := by
  classical
  have h2 : (2 * u : 𝓞 E) = (2 : ℤ) • u := by simp
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add (f := _), map_one, h2, map_smul,
    Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace (RingOfIntegers.basis E)]
  generalize Polynomial.eval (2 : ℤ) _ = c
  exact ⟨c, by ring⟩

theorem det_interp_pm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E)
    (hinj : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hA : ∀ x, φ (gam x) = A *ᵥ φ x)
    (hdet : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (T : D.La →ₗ[ℤ] D.La) (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (4 : ℤ) ∣ (LinearMap.toMatrix b b T).det - 1 := by
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  haveI := D.fin
  have hfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • A + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add (f := _), map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hA, Matrix.one_mulVec, sub_smul, one_smul])
  have hst : ∀ v ∈ LinearMap.range φ, A *ᵥ v ∈ LinearMap.range φ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨gam x, hA x⟩
  rcases hdet with hdet | ⟨hdet, h4⟩
  · obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t 1 he0 ht (LinearMap.range φ) A hfg hspan
      hst (by simpa using hdet)
    rw [hy, ← Algebra.coe_norm_int] at h
    have h1 : (H.w0 ^ 4 * 1 + (1 - H.w0 ^ 4) + (8 : ℕ) * y : 𝓞 E) = 1 + 2 * ((4 : ℤ) • y) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have h2 := norm_one_add_two ((4 : ℤ) • y)
    rw [Int.cast_injective h, h1]
    rw [map_zsmul, smul_eq_mul] at h2
    omega
  · obtain ⟨m, hm, hpow⟩ := hdet
    have hi : IsIntegral ℤ A.det := IsIntegral.of_pow hm (hpow ▸ isIntegral_one)
    obtain ⟨δ, hδ⟩ : ∃ δ : 𝓞 E, (δ : E) = A.det := ⟨⟨_, hi⟩, rfl⟩
    obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t δ he0 ht (LinearMap.range φ) A hfg hspan hst hδ.symm
    rw [hy, ← Algebra.coe_norm_int] at h
    have hrt : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hN := UpperTheory.norm_root_of_unity_quadratic_subfield E (H.rt : E) H.d H.d_prime (by have := H.d_mod; omega) hrt h4 (δ : E)
      ⟨m, hm, by rw [hδ, hpow]⟩
    have hw : ((H.w0 ^ 4 : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(H.rt : E)} := by
      have h2 : (H.w0 : E) = (1 + (H.rt : E)) / ((2 : ℕ) : E) := by
        have h3 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
          have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        rw [← h3]
        push_cast
        ring
      have h4' : ((H.w0 ^ 4 : 𝓞 E) : E) = (H.w0 : E) ^ 4 := by push_cast; rfl
      rw [h4', h2]
      exact pow_mem (div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self _ _)) (natCast_mem _ 2)) 4
    have h8 := UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one E _ 8 _ t δ y hw ht hN
    rw [Int.cast_injective h]
    exact (show (4 : ℤ) ∣ ((8 : ℕ) : ℤ) by norm_num).trans h8

theorem blocks_det_mod_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g r : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a, φ (gam a) = A *ᵥ φ a) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j)) ∧ (4 : ℤ) ∣ N.toBlocks₁₁.det - 1 := by
  intro E _ _ _ H D g r bas gam N φ A ⟨hl, hr⟩ hinj hspan hA hdet hN
  classical
  let π : D.La →+ (Fin g ⊕ Fin g → ZMod 8) :=
    { toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8)
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8) := fun _ _ => rfl
  have h8 : ∀ x, π ((8 : ℕ) • x) = 0 := fun x => by
    rw [map_nsmul]
    ext u
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0 := fun v u => by
    simp [hπ, Pi.single_apply]

  have he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u := by
    intro x u
    obtain ⟨c, rfl⟩ := bas.surjective x
    induction c using Pi.single_induction with
    | zero => cases u <;> simp
    | add a b ha hb => rw [map_add (f := _), smul_add, map_add (f := _), map_add (f := _), Pi.add_apply, ha, hb]; cases u <;> simp
    | single v n =>
      have : (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      cases v with
      | inl k =>
        obtain ⟨e, h⟩ := hl k
        rw [h, map_add (f := _), h8, add_zero]
        cases u <;> simp [hπb]
      | inr k =>
        obtain ⟨e, h⟩ := hr k
        rw [h, h8]
        cases u <;> simp [hπb]
  have hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u := fun u v => by
    rw [hN, hπ]
  constructor
  · intro i j
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hr j
      have h1 := he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)
      rw [← map_smul, h, map_nsmul, h8] at h1
      rw [hN']
      exact h1.symm
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hl j
      have h1 := he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)
      rw [← map_smul, h, map_add (f := _), map_nsmul, map_add (f := _), h8, add_zero] at h1
      rw [hN']
      exact h1
  · let b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La := (Pi.basisFun ℤ _).map bas
    let T : D.La →ₗ[𝓞 E] D.La :=
      H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)
    have hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x) := fun x => rfl
    have h := det_interp_pm D b gam φ A hinj hspan hA hdet (T.restrictScalars ℤ) hT
    suffices h8 : (8 : ℤ) ∣ N.toBlocks₁₁.det - (LinearMap.toMatrix b b (T.restrictScalars ℤ)).det by
      omega
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [Int.cast_sub, sub_eq_zero, ← eq_intCast (Int.castRingHom (ZMod 8)),
      ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]
    have hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v =
        π (T.restrictScalars ℤ (bas (Pi.single v 1))) u := fun u v => by
      simp [LinearMap.toMatrix_apply, b, hπ]
    have hblk : (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) =
        Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁)
          (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix
            (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) (Sum.inr j)) 0 1 := by
      ext u v
      rcases u with i | i <;> rcases v with j | j
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [Matrix.toBlocks₁₁, hN']
      · rfl
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb]
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb, Matrix.one_apply]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]

end GlobalTheory.AdaptedDetSign
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMove

section

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

theorem exists_entire_ratio {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (W : ι → Set V)
    (hW : ∀ i, IsOpen (W i)) (hcov : ∀ w, ∃ i, w ∈ W i) (f f' : ι → V → ℂ) (c : ι → ι → V → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (W i)) (hd' : ∀ i, DifferentiableOn ℂ (f' i) (W i))
    (hn : ∀ i, ∀ w ∈ W i, f i w ≠ 0) (hn' : ∀ i, ∀ w ∈ W i, f' i w ≠ 0)
    (hc : ∀ i j w, w ∈ W i → w ∈ W j → f i w = c i j w * f j w)
    (hc' : ∀ i j w, w ∈ W i → w ∈ W j → f' i w = c i j w * f' j w) :
    ∃ ρ : V → ℂ, Differentiable ℂ ρ ∧ (∀ w, ρ w ≠ 0) ∧ ∀ i, ∀ w ∈ W i, f' i w = ρ w * f i w := by
  choose J hJ using hcov
  have key : ∀ i, ∀ w ∈ W i, f' i w = f' (J w) w / f (J w) w * f i w := fun i w h => by
    have := hn _ _ (hJ w)
    rw [hc i (J w) w h (hJ w), hc' i (J w) w h (hJ w)]
    field_simp
  refine ⟨_, fun w => ?_, fun w => div_ne_zero (hn' _ _ (hJ w)) (hn _ _ (hJ w)), key⟩
  refine (((hd' (J w)).mul ((hd (J w)).inv (hn _))).congr fun w' h => ?_).differentiableAt ((hW _).mem_nhds (hJ w))
  exact (eq_div_of_mul_eq (hn _ _ h) (key _ _ h).symm).trans (div_eq_mul_inv _ _)


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem det_eq_sq_mul_of_theta_ratio (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ))
    (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ)
    (hbas : ∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hN : ∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) (hP : ∀ a, P' a = P (gam a))
    (hn : ∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1)
    (hn' : ∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1)
    (hτ : τ ∈ SiegelH (Fin g)) (hτ' : τ' ∈ SiegelH (Fin g)) (hu : IsUnit h.det)
    (h8 : ∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j))
    (hdet : (4 : ℤ) ∣ N.toBlocks₁₁.det - 1)
    (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0) (hρ1 : ρ 0 = 1) (hκ : κ ≠ 0)
    (hrel : ∀ z, thetaChar τ' c₁ c₂ (h' *ᵥ z) * ρ z = κ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    h.det = κ ^ 2 * h'.det := by
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H D g bas gam N
    P P' h h' τ τ' hbas hiso hN hP hn hn' hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := GlobalTheory.theta_sq_transform_level_eight g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => h⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => ρ (h⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel (h⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  rw [hde, hκ2]



theorem theta_move_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y z y' gam A ρ ν t hκ hκ' hy hz hiso hA hdA hPP hex hmv hbor
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z.x = y.x ≫ ρ := hbor.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hbor
  clear hmv
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hu, -, hv⟩ := hy
  obtain ⟨hu', -, hv'⟩ := hz
  obtain ⟨hdu, hsy, hpos, hn⟩ := T.norm b hb
  obtain ⟨hdu', hsy', hpos', hn'⟩ := T.norm b' hb'
  have hd : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b, w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b)) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b, w)) (by fun_prop) (fun w h => ⟨hb, h⟩)
  have hd' : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b', w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b')) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b', w)) (by fun_prop) (fun w h => ⟨hb', h⟩)
  have hne := fun j w => T.fr_ne j b w hb
  have hne' := fun j w => T.fr_ne j b' w hb'
  have hc := fun j j' w => T.fr_coc j j' b w hb
  have hc' := fun j j' w => T.fr_coc j j' b' w hb'
  have h0 := fun j => T.fr_rig j b hb
  have h0' := fun j => T.fr_rig j b' hb'
  generalize T.Pf (T.co b) = P at *
  generalize T.Pf (T.co b') = P' at *
  have hcov2 : ∀ w, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2 := fun w => by
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex k P w).left
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex k P w).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' w hw => by
    rw [hex]; exact ((o1 _ _ _).1 hw).1
  have tr2 : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' w hw => ((o1 _ _ _).1 hw).2
  have hw0 : ∀ w, (F.ex k P w).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P w)).trans hu.symm
  have hw0' : ∀ w, (F.ex k P' w).left ≫ Xo.univ.t.G.hom = (z.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P' w)).trans hu'.symm
  have hz0 : (F.ex k P 0).left = (y.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker k P hp 0).2 (zero_mem _), hu]
    rfl
  obtain ⟨ρf, hρd, hρ0, hfr⟩ := exists_entire_ratio
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {w | ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2})
    (fun j => GlobalTheory.FamilyUnif_isOpen_ex F k P hp _) hcov2
    (fun q w => valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) (fun q w => T.fr q.1 (b', w))
    (fun q q' w => valAt' ((F.ex k P w).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F k P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
      fun w hw => ⟨Set.mem_univ _, hw⟩).mul ((hd q.2).mono fun w hw => tr2 _ _ w hw))
    (fun q => (hd' q.1).mono fun w hw => tr _ _ w hw)
    (fun q w hw => mul_ne_zero (o2 _ _ _ hw) (hne _ w (tr2 _ _ w hw)))
    (fun q w hw => hne' _ w (tr _ _ w hw))
    (fun q q' w h1 h2 => by
      rw [hc q.2 q'.2 w ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ w h1, tr2 _ _ w h2⟩), ← mul_assoc,
        o3 _ _ _ _ _ h1 h2, mul_assoc])
    (fun q q' w h1 h2 => by
      have e2 := hc' q.1 q'.1 w ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
      rw [hex] at e2
      exact e2)
  have hρ1 : ρf 0 = 1 := by
    obtain ⟨q, hq⟩ := hcov2 0
    have e1 := hfr q 0 hq
    have e2 : T.fr q.1 (b', 0) = valAt' (F.ex k P 0).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, 0) := by
      rw [h0 _ (tr2 _ _ 0 hq), h0' _ (tr _ _ 0 hq), ← hu', hxρ]
      exact (o4 _ _ _ _ hz0 hq).trans (congrArg (fun x : Sp ℂ ⟶ Xo.X => _ * valAt' x _ _) hu)
    exact (mul_eq_right₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ 0 (tr2 _ _ 0 hq)))).1 (e1.symm.trans e2)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z.x y'.x z.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  generalize Formalism.L2.PjFree.toC (t none : CAt σ) = t₀ at *
  have hrel : ∀ w, thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * ρf w =
      κ / (t₀ * κ') * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) := fun w => by
    obtain ⟨q, hq⟩ := hcov2 w
    let p : Over.mk (y.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex k P w).left (hw0 w)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 w _ e1 e2 (tr2 _ _ w hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex k P' w).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 w pt h1 h2 (tr _ _ w hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex w)) h2 hq)
    have hval2 : valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) *
        (κ * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) * T.fr q.2 (b, w)) =
        t₀ * (κ' * thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * T.fr q.1 (b', w)) :=
      (congrArg (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    have e3 : T.fr q.1 (b', w) = ρf w * (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) :=
      hfr q w hq
    rw [e3] at hval2
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hκ')]
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ w (tr2 _ _ w hq)))
    linear_combination -hval2
  have hAu : IsUnit A.det := by
    rcases hdA with h | ⟨⟨m, hm, h⟩, -⟩
    · rw [h]; exact isUnit_one
    · exact IsUnit.of_pow_eq_one h hm.ne'
  have hdA' : A⁻¹.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A⁻¹.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E) := by
    rw [Matrix.det_nonsing_inv]
    rcases hdA with h | ⟨⟨m, hm, h⟩, h4⟩
    · left; rw [h]; simp
    · right; exact ⟨⟨m, hm, by rw [Ring.inverse_eq_inv', inv_pow, h, inv_one]⟩, h4⟩
  have hiso' : ∀ a a', (F.Di k).EF (gam.symm a) (gam.symm a') = (F.Di k).EF a a' := fun a a' => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => T.bas.symm (gam.symm (T.bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := GlobalTheory.AdaptedDetSign.blocks_det_mod_four E H (F.Di k) g r T.bas gam.symm N
    ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) A⁻¹ T.adapt
    (Subtype.val_injective.comp (M.φ k).injective)
    (by
      rw [← (M.X k).Λ_span]
      congr 1
      ext v
      exact ⟨fun ⟨a, ha⟩ => ha ▸ (M.φ k a).2, fun hv => ⟨(M.φ k).symm ⟨v, hv⟩,
        congrArg Subtype.val ((M.φ k).apply_symm_apply ⟨v, hv⟩)⟩⟩)
    (fun a => by
      have := hA (gam.symm a)
      rw [gam.apply_symm_apply] at this
      show (M.φ k (gam.symm a) : Fin r → E) = A⁻¹ *ᵥ (M.φ k a : Fin r → E)
      rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec])
    hdA' (fun _ _ => rfl)
  have hκ2 := det_eq_sq_mul_of_theta_ratio E H (F.Di k) g T.bas gam.symm N P P' (T.h b) (T.h b') (T.ta b) (T.ta b')
    T.c₁ T.c₂ ρf _ T.sympl hiso' (fun _ _ => rfl) (fun a => by rw [← hPP, gam.apply_symm_apply]) hn hn'
    ⟨hsy, hpos⟩ ⟨hsy', hpos'⟩ hdu h8 hdet T.half₁ T.half₂ hρd hρ0 hρ1
    (div_ne_zero hκ (mul_ne_zero ht0 hκ')) hrel
  rw [hκ2]
  field_simp

end GlobalTheory.GeoLevel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMoveStatement

section

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  first | exact @GlobalTheory.GeoLevel.theta_move_sq | exact GlobalTheory.GeoLevel.theta_move_sq | (intros; apply GlobalTheory.GeoLevel.theta_move_sq <;> assumption)
end
end
