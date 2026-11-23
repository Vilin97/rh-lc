module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussianStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactIsOpenCosVN
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockKStable

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockKStable : PositivityTheory.PfSWUS.FockKStable := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd k hk
  obtain ⟨𝓕, hμ⟩ := hStd.hμ
  have hψ := hStd.hψ
  have hχ := hStd.hχ
  have hr := hStd.hη
  have hθ := hStd.hθ
  have hω := hStd.hω
  have hl := hStd.hl
  have hs := hStd.hs
  have hΦ := hStd.hΦ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

end GlobalTheory.CompanionTheory.PfSWUS

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompact

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Box

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem isPureFin_box (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v))
    (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b ((GlobalTheory.CompanionTheory.WhitFree.boxF A).indicator (fun _ => (1 : ℂ)))
      (fun v => (A v).indicator 1) := by
  classical
  refine ⟨fun v => ?_, ?_, fun X => ?_⟩
  · haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
      (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space
    have hcl : IsClopen (A v) := ⟨(hA v).1.isClosed, (hA v).2⟩
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
      HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ A v
    · exact ⟨A v, (hA v).2, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        rfl⟩
    · exact ⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    refine hv ?_
    show (A v).indicator 1 = _
    rw [hS v h]
  · by_cases hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A
    · rw [Set.indicator_of_mem hX]
      exact (finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm
    · rw [Set.indicator_of_notMem hX]
      obtain ⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by
        by_contra h
        push_neg at h
        exact hX h
      refine (finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm
      have hfin := Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)
      refine (hfin.union S.finite_toSet).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h
      apply hv
      show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1
      rw [hS v h.2]
      exact Set.indicator_of_mem h.1 _

end Box

theorem exists_fin_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {P : M → Prop}
    (hs : ∀ (a : ℂ) (x : M), P x → P (a • x)) {x : M} (hx : x ∈ Submodule.span ℂ {y | P y}) :
    ∃ (N : ℕ) (f : Fin N → M), x = ∑ j, f j ∧ ∀ j, P (f j) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩
  | zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    obtain ⟨N', f', rfl, hf'⟩ := hy
    refine ⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [Fin.append_left] using hf i
    · simpa [Fin.append_right] using hf' i
  | smul a x _ hx =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    exact ⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩

variable {D : D7} {n : ℕ}

theorem evalPoly_monomial_mul {m : ℕ} (e : D.what₂.Tau × Fin m × Fin n × Bool →₀ ℕ) (a c : ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.monomial e (a * c)) z = a * evalPoly (MvPolynomial.monomial e c) z := by
  simp only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]

theorem isMonoFock_smul {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : Mx D V.rank n → ℂ} (a : ℂ)
    (h : IsMonoFock θ V l s φ) : IsMonoFock θ V l s (a • φ) := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  refine ⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]

theorem gen_mem_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  classical
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis D.host.F D.host.E
  let tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X i j => X j i
      invFun := fun Z j i => Z i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  let g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => g (tr X)
  have hg' : IsSB g' := ⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩
  obtain ⟨t, A, S, hA, hS, hdec⟩ := Box.exists_box_combN b g' hg'
  let ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)
  have hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i)
      (fun v => (A a v).indicator 1) := fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)
  have hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) =
      ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n =>
        evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) *
          gauss V l s (fun τ => compAt θ τ x) * ind a (fun i j => finPart D (x i j))) := by
    funext x
    have hp : evalPoly p (fun τ => compAt θ τ x) =
        ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
      calc evalPoly p (fun τ => compAt θ τ x)
          = evalPoly (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
            rw [← p.as_sum]
        _ = _ := by simp only [evalPoly, map_sum]
    have hgx : g (fun i j => finPart D (x i j)) =
        ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j)) :=
      hdec (fun j i => finPart D (x i j))
    rw [hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hφ]
  refine Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩

theorem fockA_le_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    fockA θ V n l s ≤ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  exact gen_mem_span θ V l s p g hg

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockSplitK : PositivityTheory.PfSWUS.FockSplitK := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk
  exact FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h)
    (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))

end GlobalTheory.CompanionTheory.PfSWUS

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompactStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fock_splitting_maximal_compact : PositivityTheory.PfSWUS.FockSplitK := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | exact GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.fockSplitK <;> assumption)
end
end
end
