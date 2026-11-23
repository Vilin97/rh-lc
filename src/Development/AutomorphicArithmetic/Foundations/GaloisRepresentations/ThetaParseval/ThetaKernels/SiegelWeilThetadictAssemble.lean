module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsFramesOfK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Frames
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Places
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.ProjInf
import Mathlib.LinearAlgebra.Matrix.CharP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.CmbVCrdV
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.BasisReprMap
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Places

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictFrames

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_of_form_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : E)
    (hY : ∀ i j, σ (d.Y.J j i) = s * d.Y.J i j) : s * ((R.ε : ℤ) : E) = 1 := by
  have hσ := sig_invol hcm
  set i0 : Fin d.n := ⟨0, d.ok.hn⟩
  have key := conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)
  rw [R.hε] at key
  simpa using key.symm
theorem zeta_of_eps_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (((R.ε : ℤ) : E) = -1 → R.ζ = 1) ∧ (((R.ε : ℤ) : E) = 1 → R.ζ = Complex.I) := by
  have h2 : (1 : E) ≠ -1 := by
    intro h
    have : (2 : E) = 0 := by linear_combination h
    exact two_ne_zero this
  constructor
  · intro h
    rcases R.hζ with ⟨_, hz⟩ | ⟨he, _⟩
    · exact hz
    · rw [he] at h; exact absurd (by simpa using h) h2
  · intro h
    rcases R.hζ with ⟨he, _⟩ | ⟨_, hz⟩
    · rw [he] at h; exact absurd (by simpa using h.symm) h2
    · exact hz
theorem exists_J_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ i j, d.A.J i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hJ : d.A.J = 0 := Matrix.ext hcon
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm := d.ok.hm
  have fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ),
      d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False := by
    intro A hrs hA
    rw [Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos d.r with hr | hr
    · have hs : 0 < d.s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
theorem not_herm_skew_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hA : d.A.IsHerm σ d.B d.r d.s) (hA' : d.A.IsSkew σ d.B d.r d.s) : False := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  have h1 := hA.herm i j
  have h2 := hA'.skew i j
  rw [h1] at h2
  have : (2 : E) * d.A.J i j = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact two_ne_zero h
  · exact hij h
theorem zeta_of_sign'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (d.A.IsHerm σ d.B d.r d.s → R.ζ = 1) ∧ (d.A.IsSkew σ d.B d.r d.s → R.ζ = Complex.I) := by
  have hcm := d.ok.good.cm
  constructor
  · intro hA
    rcases d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).1 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm (-1) (fun i j => by rw [hY]; ring)
      linear_combination -this
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA hA').elim
  · intro hA
    rcases d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA' hA).elim
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).2 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm 1 (fun i j => by rw [hY]; ring)
      linear_combination this
theorem eta_zeta'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I) := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · left
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).1 hA⟩
    have h := herm i j
    rw [map_mul, hA.herm] at h
    exact mul_right_cancel₀ hij h
  · right
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).2 hA⟩
    have h := herm i j
    rw [map_mul, hA.skew] at h
    have : (σ η + η) * d.A.J i j = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linear_combination h'
    · exact (hij h').elim
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPlaces

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isPlaces_thW'_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) : Gen.IsPlaces σ B.ψ (thW B) (fun _ => -1) := by
  have : IsTotallyReal F := hB.cm.1
  refine ⟨fun w => GlobalTheory.Mem.VolExists.infEmb_continuous (thW_infEmb B w),
    GlobalTheory.Mem.VolExists.infEmb_bijective hB.cm (isCMFam_conj B hB.cm) (fun w => thW_infEmb B w),
    fun w z => GlobalTheory.Mem.VolExists.infEmb_sigR hB.cm (thW_infEmb B w) z, fun _ => by norm_num, fun x => ?_⟩
  have hs := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).2.2 (archimedeanEmbeddingTensor B) (archimedean_embedding_family B) x
  have hs' : B.ψ ((x, 0) : AF F) = _ := hs
  change B.ψ ((x, 0) : AF F) = _
  rw [hs']
  congr 1
  have hr : ∀ w, starRingEnd ℂ (archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E))) = archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E)) := fun w => by
    rw [archimedean_embedding_tmul, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      Complex.conj_ofReal]
  simp only [thW_eq, hr]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPureB

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (w : InfinitePlace F) (X : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    Gen.crd (θ w) (fr w) (g w) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) = R.loc w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) := by
  set c : ℂ := ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcdef
  have hm : Nonempty (Fin d.m) := ⟨⟨0, d.ok.hm⟩⟩
  have hc : c ≠ 0 := by
    intro h0
    have h1 := frc w
    rw [← hcdef, h0, zero_smul] at h1
    have h2 : ((fr w)⁻¹).1 * (fr w).1 = 1 := Units.inv_mul (fr w)
    rw [h1, Matrix.mul_zero] at h2
    exact zero_ne_one h2
  have hfr : ((fr w)⁻¹).1 = c⁻¹ • (((R.fr w)⁻¹).1).map star := by
    refine Units.inv_eq_of_mul_eq_one_left ?_
    rw [frc w, ← hcdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← map_star_mul,
      Units.inv_mul]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hN : ((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star = 1 := by
    rw [← map_star_mul, ← Matrix.transpose_mul]
    have : d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1 * d.cw w u.1 = 1 := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
      rw [← Matrix.map_mul (f := piInf (d.B.emb w)), Units.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.transpose_one]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hg : (g w).1 = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
    calc (g w).1 = (g w).1 * (((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star) := by
          rw [hN, Matrix.mul_one]
      _ = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
          rw [← Matrix.mul_assoc, gc w, ← hcdef, Matrix.smul_mul, Matrix.one_mul]
  have hX : Matrix.of (fun a j => θ w (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j a)) = (d.cw w (toMx X)).map star := by
    ext a j
    simp only [Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projInf, th, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, toMx]
  have hZ : d.cw w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) =
      d.cw w (toMx X) * (d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
    rw [Matrix.map_mul (f := piInf (d.B.emb w)), Matrix.transpose_map]
  unfold Gen.crd _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [hfr, hX, hg, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    map_star_mul, map_star_mul, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPure

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem pure_prod_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf)
    (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (l : InfinitePlace F → ℝ) (hl : ∀ w, |l w| = 1) :
    ∃ (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin (fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ))
        (Gen.phiInf θ l fr g P) Φf := by
  obtain ⟨hloc, hcof, hT⟩ := hP
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ :=
    fun v Y => gf v (crdV d.bs v (toMxV v Y * Av u v))
  refine ⟨fun X => ∏ᶠ v, Φv v (HeckeCharacterZeroLocus.SiegelWeilU.projV v X), Φv,
    ⟨fun v => isSB_comp d.bs u v (gf v) (hloc v), ?_, fun X => rfl⟩, ?_⟩
  · filter_upwards [hcof, int_iff (m := d.m) d.bs u] with v hv hint
    funext Y
    show gf v _ = _
    rw [hv]
    by_cases h : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV d.bs v
    · rw [Set.indicator_of_mem h]
      refine (Set.indicator_of_mem ?_ _).trans rfl
      exact (hint Y).2 h
    · rw [Set.indicator_of_notMem h]
      refine Set.indicator_of_notMem ?_ _
      intro h'
      exact h ((hint Y).1 h')
  · intro X
    dsimp only
    rw [hT]
    dsimp only
    congr 1
    · unfold Gen.phiInf
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB.crd_eq_k R u η θ th fr frc g gc w X, hl w, mul_one]
      rfl
    · refine finprod_congr fun v => ?_
      congr 1
      funext k
      have hZ : (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map (mapV v) =
          toMxV v (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) * Av u v := by
        rw [map_mul_alg]
        congr 1
        ext a j
        simp only [Matrix.map_apply, toMx, toMxV, Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin,
          mapV_eq]
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k).2 =
          phiV v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k) := rfl
      rw [h1, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictAssemble

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
def RelRealP_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
  ∀ η : E, η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
    (∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)) ∧
    (∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) ∧
    (∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1) ∧
    (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf
theorem relReal_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k := by
  intro F E _ _ _ _ _ σ d R Φ P gf hP x t u _ η hη herm
  obtain ⟨Φf, Φv, hpf, hpr⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.pure_prod_of'_k R Φ P gf hP u η (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w)
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w) (fun _ => -1) (fun _ => by norm_num)
  refine ⟨thW d.B, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη, fun _ => -1, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η, _, Φf, Φv, thW_th' d.B, fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w,
    fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w, fun _ => rfl, ⟨fun w => decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re), rfl⟩,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isCharAF_of_good_k d.B d.ok.good, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isPlaces_thW'_k d.B d.ok.good,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isFrames_of'_k R η hη d.ok.good.cm herm (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eta_zeta'_k R hη herm) (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη)
      (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w), hpf, hpr⟩
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end
