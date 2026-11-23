module

public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.ShiftInvariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Formalism.HermitianLattices.StatementLat
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometricallyStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublattice

section

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.SubReal

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  rw [Complex.ofReal_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_isometry {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]
    (P : Matrix m k ℂ) (h : Pᴴ * P = 1) (u : k → ℂ) :
    cnorm (P *ᵥ u) = cnorm u := by
  have hsum : (∑ i, ‖(P *ᵥ u) i‖ ^ 2 : ℝ) = ∑ i, ‖u i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      h, Matrix.vecMul_one]
  unfold cnorm
  rw [hsum]

theorem exists_isometry_factor {n j : ℕ} (Y : Matrix (Fin n) (Fin j) ℂ)
    (L : Matrix (Fin j) (Fin n) ℂ) (hL : L * Y = 1) :
    ∃ (Z : Matrix (Fin j) (Fin j) ℂ) (P : Matrix (Fin n) (Fin j) ℂ),
      IsUnit Z.det ∧ Pᴴ * P = 1 ∧ Y = P * Z⁻¹ := by
  classical
  have hG0 : (0 : Matrix (Fin j) (Fin j) ℂ) ≤ Yᴴ * Y := (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg
  obtain ⟨S, hSS, hSh⟩ : ∃ S : Matrix (Fin j) (Fin j) ℂ, S * S = Yᴴ * Y ∧ Sᴴ = S :=
    ⟨CFC.sqrt (Yᴴ * Y), CFC.sqrt_mul_sqrt_self _ hG0, (CFC.sqrt_nonneg (Yᴴ * Y)).isSelfAdjoint⟩
  have hker : ∀ x : Fin j → ℂ, (Yᴴ * Y) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hYx : Y *ᵥ x = 0 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero Y x).mp hx
    have hback : L *ᵥ (Y *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rw [← hback, hYx, Matrix.mulVec_zero]
  have hGu : IsUnit (Yᴴ * Y).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv (hker v hv0)
  have hSu : IsUnit S.det := by
    have h2 : IsUnit (S * S).det := by rw [hSS]; exact hGu
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨S⁻¹, Y * S⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact hSu.ringInverse
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Yᴴ, ← hSS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hSu]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hSu, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu,
      Matrix.mul_one]

theorem fcoord_std {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (x : Fin d → K) :
    fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold fcoord vecAt
  simp only [Pi.basisFun_repr]

end GlobalTheory.SubReal


open GlobalTheory.SubReal in
theorem GlobalTheory.exists_isometric_realisation_of_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  intro K _ _ _ _ n X R hX hR
  classical
  let bS := Module.finBasis K (Submodule.span K (R : Set (Fin n → K)))
  let ψ : (Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K) →ₗ[K] (Fin n → K) :=
    (Submodule.span K (R : Set (Fin n → K))).subtype ∘ₗ bS.equivFun.symm.toLinearMap
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype _).comp bS.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ψ (LinearMap.ker_eq_bot.mpr hinj)
  have hgψ : ∀ y, g (ψ y) = y := fun y => LinearMap.congr_fun hg y
  have hψS : ∀ y, ψ y ∈ Submodule.span K (R : Set (Fin n → K)) := fun y => Submodule.coe_mem _
  have hψg : ∀ r ∈ Submodule.span K (R : Set (Fin n → K)), ψ (g r) = r := by
    intro r hr
    obtain ⟨y, rfl⟩ : ∃ y, ψ y = r := ⟨bS.equivFun ⟨r, hr⟩, by simp [ψ]⟩
    rw [hgψ]
  have hψR : ∀ r ∈ R, ψ (g r) = r := fun r hr => hψg r (Submodule.subset_span hr)
  have hi : ∀ y, LinearMap.toMatrix' ψ *ᵥ y = ψ y := fun y => LinearMap.toMatrix'_mulVec ψ y
  have hLi : LinearMap.toMatrix' g * LinearMap.toMatrix' ψ = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLY : ∀ w : InfinitePlace K,
      ((LinearMap.toMatrix' g).map w.embedding * X w) *
        ((X w)⁻¹ * (LinearMap.toMatrix' ψ).map w.embedding) = 1 := by
    intro w
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X w), Matrix.mul_nonsing_inv _ (hX w), Matrix.one_mul,
      ← Matrix.map_mul, hLi, Matrix.map_one _ (map_zero _) (map_one _)]
  choose Z P hZ hP hY using fun w => exists_isometry_factor _ _ (hLY w)
  have hmap : (R.map (g.restrictScalars (𝓞 K))).map (ψ.restrictScalars (𝓞 K)) = R := by
    ext r
    constructor
    · rintro ⟨y, ⟨r', hr', rfl⟩, rfl⟩
      simpa [hψR r' hr'] using hr'
    · intro hr
      exact ⟨g r, ⟨r, hr, rfl⟩, hψR r hr⟩
  have hnorm : ∀ (v : InfinitePlace K) (x : Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K),
      normAt (Pi.basisFun K (Fin n)) X v (ψ x) = normAt (Pi.basisFun K _) Z v x := by
    intro v x
    unfold normAt
    rw [fcoord_std, fcoord_std]
    have hcomp : (fun k => v.embedding (ψ x k)) =
        (LinearMap.toMatrix' ψ).map v.embedding *ᵥ fun k => v.embedding (x k) := by
      funext k
      rw [← hi x, RingHom.map_mulVec]
      rfl
    rw [hcomp, Matrix.mulVec_mulVec, hY v, ← Matrix.mulVec_mulVec, cnorm_mulVec_isometry _ (hP v)]
  have hRR := (Formalism.HN.rerealize K _ _ (Fin n → K) (Fin n) (Pi.basisFun K _) Z (Pi.basisFun K (Fin n)) X ψ
    hZ hX hinj hnorm (R.map (g.restrictScalars (𝓞 K))) (hR.map _)).2.2.2.2.2.2
  refine ⟨Module.finrank K (Submodule.span K (R : Set (Fin n → K))), LinearMap.toMatrix' ψ, Z, P,
    R.map (g.restrictScalars (𝓞 K)), rfl, hZ, hP, hY, hR.map _, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, eq_top_iff]
    intro y _
    exact ⟨ψ y, hψS y, hgψ y⟩
  · rintro y ⟨r, hr, rfl⟩
    rw [hi]
    simpa [hψR r hr] using hr
  · intro r hr
    exact ⟨g r, ⟨r, hr, rfl⟩, by rw [hi]; exact hψR r hr⟩
  · rw [← hRR, hmap]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublatticeStatement

section

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_isometric_realisation_of_sublattice' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  first | exact @GlobalTheory.exists_isometric_realisation_of_sublattice | exact GlobalTheory.exists_isometric_realisation_of_sublattice | (intros; apply GlobalTheory.exists_isometric_realisation_of_sublattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiusHomSubquotientSublattice

section

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.SubquotCover

theorem sum_normSq_eq_trace {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_normSq_mul {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c]
    (P : Matrix a b ℂ) (M : Matrix b c ℂ) (Q : Matrix c d ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) :
    ∑ i, ∑ j, ‖(P * M * Q) i j‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, conjTranspose_mul, conjTranspose_mul]
  have hmid : Qᴴ * (Mᴴ * Pᴴ) * (P * M * Q) = Qᴴ * (Mᴴ * M * Q) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]
  rw [hmid, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem vecAt_mulVec {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (w : InfinitePlace K) (M : Matrix (Fin a) (Fin b) K) (y : Fin b → K) :
    vecAt (Pi.basisFun K (Fin a)) w (M *ᵥ y)
      = M.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin b)) w y := by
  funext i

  simp only [vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
  map_mul]

theorem mulVec_fcoord {K : Type} [Field K] [NumberField K] [StarRing K] {a : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (w : InfinitePlace K) (hX : IsUnit (X w).det) (y : Fin a → K) :
    X w *ᵥ fcoord (Pi.basisFun K (Fin a)) X w y = vecAt (Pi.basisFun K (Fin a)) w y := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

theorem subquot_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N S) → largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ n X A S R lo hi hX hA hSat hR hlo hhi hsize hlarge T hTS hTR
  obtain ⟨m, q, X', Q, hm, hX', hQ, hqf, -, hQS, hqS, hspan, hN⟩ :=
    GlobalTheory.T.quotient_lattice_realized_isometrically K n X A S hX hA hSat
  obtain ⟨r, e, X'', P, B, hr, hX'', hP, hPe, hB, hBspan, heB, hRB, hlB⟩ :=
    GlobalTheory.T.exists_isometric_realisation_of_sublattice' K n X R hX hR
  obtain ⟨φ', hφ'B, hbound⟩ := GlobalTheory.T.lattice_pair_volume_bounds K m r X' X''
    (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) B lo hi hX' hX'' (hA.map _) hB hspan
    hBspan hlo hhi
    (fun N' hN' hN'0 => by
      obtain ⟨N, hSN, hNA, heq⟩ := hN N' hN' hN'0
      rw [← heq]
      exact hsize N hSN hNA)
    (by rw [hlB]; exact hlarge) (fun w => (P w)ᴴ * T w * (Q w)ᴴ)
  refine ⟨e * φ' * q, ?_, ?_,
    fun w => P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w,
    ?_, ?_⟩
  · intro y hy
    rw [← Matrix.mulVec_mulVec, hqS y hy, Matrix.mulVec_zero]
  · intro y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply heB
    apply hφ'B
    exact Submodule.mem_map.mpr ⟨y, hy, by simp [Matrix.toLin'_apply]⟩
  · intro w y hy
    set u := fcoord (Pi.basisFun K (Fin n)) X w y with hu
    have hQu : Q w *ᵥ u = fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) := (hqf w y hy).symm
    have hXu : X w *ᵥ u = vecAt (Pi.basisFun K (Fin n)) w y := mulVec_fcoord X w (hX w) y
    have hX'u : X' w *ᵥ (Q w *ᵥ u) = q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y := by
      rw [hQu, mulVec_fcoord X' w (hX' w), vecAt_mulVec]

    have hTQ : T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u)) = T w *ᵥ u := by
      have hmem : u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
          Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
        hQS w u (Submodule.subset_span ⟨y, hy, rfl⟩)
      have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))
          ≤ LinearMap.ker (Matrix.mulVecLin (T w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact hTS w z hz
      have h0 := hker hmem
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero] at h0
      exact h0.symm

    have hPP : ∀ v ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))),
        P w *ᵥ ((P w)ᴴ *ᵥ v) = v := by
      intro v hv
      have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))
          ≤ LinearMap.range (Matrix.mulVecLin (P w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, -, rfl⟩ := hRB x hx
        refine ⟨(X'' w)⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin r)) w z, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPe w, ← Matrix.mulVec_mulVec,
          ← vecAt_mulVec]
        rfl
      obtain ⟨z, rfl⟩ := hle hv
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec _ (P w)ᴴ, hP w, Matrix.one_mulVec]
    calc (P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w) *ᵥ u
        = P w *ᵥ ((P w)ᴴ *ᵥ (T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u))))
          - (P w * (X'' w)⁻¹) *ᵥ (φ'.map w.embedding *ᵥ (X' w *ᵥ (Q w *ᵥ u))) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
      _ = T w *ᵥ u - ((X w)⁻¹ * e.map w.embedding) *ᵥ (φ'.map w.embedding *ᵥ
            (q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y)) := by
          rw [hTQ, hPP _ (hTR w y hy), hX'u, hPe w]
      _ = (T w - (X w)⁻¹ * (e * φ' * q).map w.embedding * X w) *ᵥ u := by
          rw [Matrix.sub_mulVec, ← hXu, Matrix.map_mul, Matrix.map_mul]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have hm' : (m : ℝ) = (rkK A : ℝ) - rkK S := by rw [← hm]; push_cast; ring
    have hr' : (r : ℝ) = rkK R := by rw [hr]
    rw [← hm', ← hr']
    refine Eq.trans_le ?_ hbound
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Formalism.REAL.hs]
    exact sum_normSq_mul (P w) _ (Q w) (hP w) (hQ w)

end GlobalTheory.SubquotCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiusHomSubquotientSublatticeStatement

section

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.coveringRadius_hom_subquotient_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ Formalism.HN.sizeQ (Pi.basisFun K (Fin n)) X N S) → Formalism.HN.largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (Formalism.HN.nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  first | exact @GlobalTheory.SubquotCover.subquot_cover | exact GlobalTheory.SubquotCover.subquot_cover | (intros; apply GlobalTheory.SubquotCover.subquot_cover <;> assumption)
end
end
