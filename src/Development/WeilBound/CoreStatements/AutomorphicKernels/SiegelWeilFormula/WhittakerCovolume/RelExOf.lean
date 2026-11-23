module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Frames
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.NormInvMulSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Places
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.CmbVCrdV
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.ProjInf
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SdEx

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.PureProdOf

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_prod_of' {d : SD σ} (R : RD d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : IsPureBy R Φ P gf)
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
      rw [PureB.crd_eq R u η θ th fr frc g gc w X, hl w, mul_one]
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
      rw [h1, SD.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Assemble

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

def RelRealP : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (Φ : d.Fn) P gf, IsPureBy R Φ P gf →
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
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (Jd d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf

theorem relReal : RelRealP := by
  unfold RelRealP
  intro F E _ _ _ _ _ σ d R Φ P gf hP x t u hx η hη herm
  have hB : d.B.IsGood σ := d.ok.good
  obtain ⟨Φf, Φv, hpf, hprod⟩ := pure_prod_of' R Φ P gf hP u η (thW d.B) (thW_th' d.B)
    (frW R η hη) (frW_frc R η hη) (gW d u η hη) (gW_gc d u η hη) (fun _ => -1) (fun _ => by simp)
  exact ⟨thW d.B, frW R η hη, gW d u η hη, fun _ => -1, εsW R η,
    fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ), Φf, Φv,
    thW_th' d.B, frW_frc R η hη, gW_gc d u η hη, fun _ => rfl,
    ⟨fun w => decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re), rfl⟩,
    isCharAF_of_good d.B hB, isPlaces_thW' d.B hB,
    isFrames_of' R η hη hB.cm herm (eta_zeta' R hη herm) (thW d.B) (thW_th' d.B) (frW R η hη) (frW_frc R η hη),
    hpf, hprod⟩

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelExOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem relEx_of (hA : RelAlg) (hS : SdEx) (hR : ThetaDictR.RelRealP) : RelEx := by
  intro _ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd
  obtain ⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩ := hA F E σ d
  obtain ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
  obtain ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
    hR F E σ d R Φ P gf hP x t u hx η hη hherm
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := hS F E σ hcm d.m (Jd d η) hJ d.B.ψ hchr d.n
  exact ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs,
    hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩

theorem relEx : RelEx := relEx_of relAlg_pf sdEx ThetaDictR.relReal

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end
