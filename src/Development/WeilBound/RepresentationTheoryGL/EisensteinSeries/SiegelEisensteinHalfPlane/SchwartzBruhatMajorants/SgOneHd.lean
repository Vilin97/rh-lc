module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapHalfTr
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionEmbeddingAlgebraMapOfTotallyReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsParComap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JMapVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapScalarVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TriangularLowerRightDiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.SgOneOfParts

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleMapMemIntAdIff

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.RgEisBInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_below_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 E), below F w = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (hker.le.trans bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact hker
  exact ⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩

theorem adeleMap_mem_intAd_iff (x : 𝔸[F]) : adeleMap F E x ∈ intAd E ↔ x ∈ intAd F := by
  have key : ∀ w : HeightOneSpectrum (𝓞 E),
      finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔
        finEval (below F w) x ∈ (below F w).adicCompletionIntegers F := by
    intro w
    haveI := liesOver_below (K := F) w
    haveI := w.isPrime
    have h1 : finEval w (adeleMap F E x) =
        SemiLocal.completionMap (below F w) w (finEval (below F w) x) :=
      finiteAdeleMap_apply x.2 w
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      SemiLocal.valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := exists_below_eq (E := E) v
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 (h _)

theorem nuCM_eqv (x : 𝔸[F]) : eqv F E (nuCM F E x) = adeleMap F E x := by
  have h := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x
  exact h

theorem bInt : BInt := by
  unfold BInt ForCM
  intro F E _ _ _ _ _ σ χ c _ _ _ _ x
  simp only [adCM, Subring.mem_comap]
  change eqv F E (nuCM F E x) ∈ intAd E ↔ _
  rw [nuCM_eqv, adeleMap_mem_intAd_iff]

end GlobalTheory.CompanionTheory.RgEisBInt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCM

section

@[expose] public section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.SgOneBase

theorem baseCM : CMGood → BFix → BRat → BInt → BInf → BLg → BDel → BaseCM := by
  intro _ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε
  obtain ⟨hνc, hνi, hνfix, r, hrc, hrfix⟩ := hFix F E σ χ c hCM hUn hHk hRes
  obtain ⟨hrat, hrat'⟩ := hRat F E σ χ c hCM hUn hHk hRes
  have hint := hInt F E σ χ c hCM hUn hHk hRes
  obtain ⟨hinf, hinf'⟩ := hInf F E σ χ c hCM hUn hHk hRes
  obtain ⟨hlg, hlgσ⟩ := hLg F E σ χ c hCM hUn hHk hRes
  obtain ⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩ := hDel F E σ χ c hCM hUn hHk hRes
  have hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x) := by
    intro x
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  let f : IdeleGroup F →* Circle := χ.comp (Units.map (nuCM F E).toMonoidHom)
  have hker : (IdeleGroup.diagonal F).range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) :=
      Units.ext (hrat a)
    show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1
    rw [e]
    exact hHk.2 _
  have hfc : Continuous f := hHk.1.comp (Continuous.units_map _ hνc)
  let ω : HeckeCharacter F :=
    ⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩
  have hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x) := fun x => rfl
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩
    rw [hσi, hσδ, map_neg]
    simp
  · refine ⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩
    · simp
    · simp
    · simpa using (adCM σ χ).O.one_mem
    · simpa using (adCM σ χ).O.one_mem
    · intro w
      simp

end GlobalTheory.CompanionTheory.SgOneBase
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat

section

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop

section

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.BlgOfDict

section

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisSo.Hd

theorem blg_of_dict : Dict → BLg := by
  intro hD F E _ _ _ _ _ σ χ c hσ _ _ _
  obtain ⟨-, -, -, -, h5⟩ := hD F E
  have key : ∀ x : (IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, (adCM σ χ).lg x =
      Real.log (GlobalTheory.Doubling.absE F E x : ℝ) := fun x => by
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = _
    rw [h5]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have e : Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x) =
        GroundTheory.Global.ideleEmbedding F E x := by
      apply Units.ext
      exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x)) : ℝ) =
      2 * Real.log (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ)
    rw [e, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F),
      GroundTheory.Global.ideleNorm_ideleEmbedding, hσ.2.2.1, map_pow]
    have : (((GroundTheory.Global.IdeleGroup.ideleModule F x) ^ 2 : {r : ℝ // 0 < r}) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ) ^ 2 := rfl
    rw [this, Real.log_pow]
    norm_num
  · rw [key, key]
    have e : Units.map (adCM σ χ).σ.toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
      apply Units.ext
      rfl
    rw [e, GlobalTheory.Doubling.absE_conjUnit]
end GlobalTheory.CompanionTheory.RgEisSo.Hd
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd

section

@[expose] public section

namespace PositivityTheory.RgEis.So

theorem sgOne_hd : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := fun sl _ sc sg dict _ cg gt bl el pl mg =>
  have jt := GlobalTheory.CompanionTheory.EisSo.jtop
  have jc := GlobalTheory.CompanionTheory.RgEisSo.jcpt sg gt jt
  have ji := GlobalTheory.CompanionTheory.RgEisSo.JIwaAd.jiwa sg
  have jch := GlobalTheory.CompanionTheory.EisSo.jCh sg bl jt
  sgOne_of_parts
    (GlobalTheory.CompanionTheory.SgOneBase.baseCM cg GlobalTheory.CompanionTheory.RgEisFix.bFix GlobalTheory.CompanionTheory.EisBrat.brat GlobalTheory.CompanionTheory.RgEisBInt.bInt GlobalTheory.CompanionTheory.RgEisSo.bInf (GlobalTheory.CompanionTheory.RgEisSo.Hd.blg_of_dict dict) GlobalTheory.CompanionTheory.CMDelta.bDel)
    GlobalTheory.CompanionTheory.RgEis.Cover.jEx jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat (GlobalTheory.CompanionTheory.EisSec.jSec_of_top jt) jch
    (GlobalTheory.CompanionTheory.EisJMir.jmir sg gt bl el pl jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat jch) (GlobalTheory.CompanionTheory.RgDescendWall.descend2 sl) (GlobalTheory.CompanionTheory.RgEisTwist.twist sl) sc cg gt pl mg

end PositivityTheory.RgEis.So
end
end
