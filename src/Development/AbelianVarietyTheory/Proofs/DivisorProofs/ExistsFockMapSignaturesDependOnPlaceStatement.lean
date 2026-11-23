module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutatorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlaceStatement
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignature
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignatures

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.FockVacuum

noncomputable section

namespace GlobalTheory.HoweD

section Sign

variable {ι : Type} {P Q R S : ι → ℕ}

def cplxD (ι : Type) (P Q R S : ι → ℕ) : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

theorem cplxD_apply (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

theorem cplxD_cplxD (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) : cplxD ι P Q R S (cplxD ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]

theorem herm_cplxD [Fintype ι] (c c' : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplxD ι P Q R S c w a b * star (cplxD ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

theorem herm_cplxD_pos [Fintype ι] (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

theorem cplxD_single [DecidableEq ι] (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := by
  ext w' a' b'
  rw [cplxD_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

theorem exists_vacuumD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]

    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD
    (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplxD _ P Q R S c = (lineSign a b).re • c' := cplxD_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplxD _ P Q R S c) x
  rw [cplxD_cplxD] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.HoweD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignaturesStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.HoweD.exists_vacuumD | exact GlobalTheory.HoweD.exists_vacuumD | (intros; apply GlobalTheory.HoweD.exists_vacuumD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignatureStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  first | exact @GlobalTheory.CCRFock.fock_map_of_ccr_dep | exact GlobalTheory.CCRFock.fock_map_of_ccr_dep | (intros; apply GlobalTheory.CCRFock.fock_map_of_ccr_dep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlace

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem exists_isFockMapD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.HoweD

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_fockMap_signatures_depend_on_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  exact GlobalTheory.HoweD.exists_isFockMapD F E σ α β κ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
end
end
