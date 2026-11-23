module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitaryDensity.EqTopOfLines
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
public import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero
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
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
public import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe
public import Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
public import Development.WeilBound.ThetaLifts.SmallCones.SoStab
public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
public import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstFin

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem coefLine_of (hS : SWFull) (hX : BoxSec) (hW : DblW) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hR : PairsStable) (hM : MatchEx) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : CoefLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t lam hl y hy Ψ hΨ
  have T := h.triple
  have l1 := T.geo.lt
  have l2 := T.geo.aBig
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ T.base (Or.inl T.geo.hV') (by omega)
  obtain ⟨q1, q2⟩ := (hM F E σ B a a' G X om om' R Rf h).2.2 _ _ hy.1 hy.2
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) _ q1
  have s2 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ q2.1
  have s3 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ hΨ
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega))
  have rp : ∀ s u, IsRapid (comb G om om' s u y) := fun s u =>
    cW.rapid (((c1 _ s1).const_smul s).add ((c2 _ s2).const_smul u)) fun γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_inv G.M (b1 _ s1).2.1 γ hγ, I_inv G.M' (b2 _ s2).2.1 γ hγ]
  have tr : ∀ s u g, (fun h => comb G om om' s u y (h * g)) = comb G om om' s u (om (1, g) y.1, om' (1, g) y.2) := fun s u g =>
    funext fun h => by simp only [comb, Pi.add_apply, Pi.smul_apply, I_right]
  obtain ⟨dd, om₂, S, l, d1, d2, d3, -⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)
  obtain ⟨⟨K, ht, k1, k2, k3, k4⟩, e, ce, he⟩ := hH F E σ B _ G.W _ _ T.base (.inr T.geo.hW)
  obtain ⟨t₀, hi⟩ := hT F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K ht e k1 k2 he μ hμ
  have sec := hX F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inr T.geo.hW) (by omega) cW T.chars.heckeα he ce
    (hK F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K k1) k2 k3 k4 sec.cont sec.law hE hμ hD hi
  have key := An.ident hE.isOpen hE.conn (hol _ (rp s t)) ((hol _ (rp 0 1)).const_mul lam) (fun z hz => ⟨(far z hz).1, by
    simp only [(far z hz).2.2 _ (rp s t), (far z hz).2.2 _ (rp 0 1), tr, ← integral_const_mul,
      fun g => hl _ ((hR F E σ B a a' G X om om' R Rf h hp hq).2 y hy g) y hy]
    exact integral_congr_ae (.of_forall fun g => mul_left_comm _ _ _)⟩) u
  haveI := cW.sc; haveI := cV.sc; haveI := cW.lc; haveI := cV.lc
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cV.fin _ _ T.geo.hM'.haar T.geo.hM'.dom⟩
  have val : ∀ φ, IsRapid φ → kpair X.α e μ D (Ê (((a' : ℂ) - (a + a' : ℕ)) / 2)) φ =
      2 * ((G.M'.μ.real G.M'.dom)⁻¹ : ℝ) * pet G.M'.μ G.M'.dom (th om' μ D φ Ψ) (th om' μ D φ Ψ) := fun φ hφ => by
    have := An.at_value (μ.restrict D) (G.M'.μ.restrict G.M'.dom) ⟨(b2 _ s3).1, cV.bdd₂ cW (b2 _ s3).1 (b2 _ s3).2.1⟩
      ⟨hφ.1, cW.bdd hφ.1 hφ.2.1⟩
    refine Eq.trans ?_ (congrArg _ this)
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, if_neg (show ¬ a + a' < a' by omega), setAverage_eq, Complex.real_smul,
      ← fun g => (((d2 Ψ s3 Ψ s3).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  rw [val _ (rp s t), val _ (rp 0 1), mul_left_comm lam] at key
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (cV.vol_ne T.geo.hM'.haar T.geo.hM'.dom)))) key

end GlobalTheory.ThK.Dbl

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.PolFin

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem polFin {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : IsPair B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  have hfS : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  change ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
    ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U at hfS
  obtain ⟨U, h0, h1⟩ := hfS
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA

end GlobalTheory.ThK.Dbl

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.PairsIrrOfArch

section

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem polFinTri : PolFin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => polFin (PositivityTheory.ThKG.pairV h)

theorem pairsIrr_of_arch (hO : PositivityTheory.ThKF.ArchOp) : PairsIrr :=
  pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri

end GlobalTheory.ThK.Dbl
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.PairsFin

section

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.PolZero

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x => by
  unfold Model.I
  have e : ∀ g, theta om Φ g (γ * x) = theta om Φ g x := fun g => by simpa only [one_mul] using h 1 (one_mem _) γ hγ g x
  simp only [e]

theorem swap_bdd {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : A × B → ℂ} (c : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∫ a, ∫ b, f (a, b) ∂ν ∂μ = ∫ b, ∫ a, f (a, b) ∂μ ∂ν :=
  integral_integral_swap (f := fun a b => f (a, b)) (Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC))

theorem int_th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Ψ : Fn F n d}
    (cX : Cpt σ X.J) (cW : Cpt σ W.J) (h1 : M.μ.IsHaarMeasure) (h2 : IsFundamentalDomain (ratU σ X.J) M.dom M.μ)
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Ψ x.1 x.2)
    (hi : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Ψ (γ * g) (γ' * h) = theta om Ψ g h)
    {φ : UA σ W.J → ℂ} (pc : Continuous φ) (pi : ∀ γ ∈ ratU σ W.J, ∀ g, φ (γ * g) = φ g) :
    ∫ g in M.dom, th om μ D φ Ψ g ∂M.μ = pet μ D φ (M.I om Ψ) := by
  haveI := cX.sc; haveI := cW.sc
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 (cX.fin _ _ h1 h2).ne
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have c : Continuous fun x : UA σ X.J × UA σ W.J => φ x.2 * star (theta om Ψ x.1 x.2) := (pc.comp continuous_snd).mul hc.star
  obtain ⟨C, hC⟩ := cX.bdd₂ cW c fun γ hγ δ hδ g g' => by simp only [pi δ hδ, hi γ hγ δ hδ]
  unfold th pet Model.I
  refine (swap_bdd _ _ c hC).trans <| integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]
  exact congrArg _ integral_conj

theorem polZero_of (hC : CptAll) (hH : HermLine) (hL : CoefLine) (hT : ThConst) (hN : NonZeroAn) (hM : MatchEx)
    (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : PolZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq
  have t := h.triple
  have cW := hC F E σ B _ G.W _ _ t.base (Or.inr t.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ t.base (Or.inl t.geo.hV') (by omega)
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨m1, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1
  have s1 : ∀ y ∈ pairs B G X R Rf, y.1 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ (m3 _ _ hy.1 hy.2).1
  have s2 : ∀ y ∈ pairs B G X R Rf, y.2 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ (m3 _ _ hy.1 hy.2).2.1
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1 (Or.inr (by omega))
  have cc : ∀ s u, ∀ y ∈ pairs B G X R Rf, Continuous (comb G om om' s u y) := fun s u y hy =>
    ((c1 _ (s1 y hy)).const_smul s).add ((c2 _ (s2 y hy)).const_smul u)
  have ci : ∀ s u, ∀ y ∈ pairs B G X R Rf, ∀ γ ∈ ratU σ G.W.J, ∀ g, comb G om om' s u y (γ * g) = comb G om om' s u y g :=
    fun s u y hy γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_left G.M (b1 _ (s1 y hy)).2.1 γ hγ, I_left G.M' (b2 _ (s2 y hy)).2.1 γ hγ]
  have e01 : ∀ y, comb G om om' 0 1 y = G.M'.I om' y.2 := fun y => by simp [comb]
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have ig : ∀ s u s' u', ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      Integrable (fun g => comb G om om' s u y g * star (comb G om om' s' u' y' g)) (μ.restrict D) := fun s u s' u' y hy y' hy' => by
    have c := (cc s u y hy).mul (cc s' u' y' hy').star
    obtain ⟨C, hC⟩ := cW.bdd c fun γ hγ g => by
      change comb G om om' s u y (γ * g) * star (comb G om om' s' u' y' (γ * g)) =
        comb G om om' s u y g * star (comb G om om' s' u' y' g)
      rw [ci s u y hy γ hγ, ci s' u' y' hy' γ hγ]
    exact Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨c, hc⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 0 0 1
  have orth : ∀ y ∈ pairs B G X R Rf, pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) = 0 := fun y hy => by
    have e : pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) =
        pet μ D (comb G om om' 1 0 y) (comb G om om' 0 1 y) - c * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y) := by
      unfold pet
      rw [← integral_const_mul, ← integral_sub (ig _ _ _ _ y hy y hy) ((ig _ _ _ _ y hy y hy).const_mul c)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hc y hy y hy, sub_self]
  obtain ⟨lam, hl⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) 1 (-c)
  obtain ⟨⟨Φ₀, q1, q2⟩, Φ', r1, r2⟩ := And.imp (fun f => f hp) (fun f => f hq) (hN F E σ B a a' G X om om' t)
  obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
  have hy : (Φ, Φ') ∈ pairs B G X R Rf := ⟨r1.2, hΦ⟩
  have v0 := cV.vol_ne t.geo.hM'.haar t.geo.hM'.dom
  have key : ∀ s u, th om' μ D (comb G om om' s u (Φ, Φ')) Φ' =
      fun _ => pet μ D (comb G om om' s u (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) / (G.M'.μ.real G.M'.dom : ℂ) := fun s u => by
    have k := (hT F E σ B a a' G X om om' R Rf h s u (fun y hy => cW.rapid (cc s u y hy) (ci s u y hy)) μ D hμ hD _ hy).2 Φ'
      (s2 _ hy)
    have i := int_th G.M' cV cW t.geo.hM'.haar t.geo.hM'.dom hμ hD (b2 _ (s2 _ hy)).1 (b2 _ (s2 _ hy)).2.1 (cc s u _ hy) (ci s u _ hy)
    simp only [k, setIntegral_const, Complex.real_smul] at i
    funext g
    rw [k, e01, ← i, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 v0)]
  have n0 : pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) ≠ 0 := fun h0 =>
    r2 (e01 (Φ, Φ') ▸ cW.eq_zero hμ hD (cc 0 1 _ hy) (ci 0 1 _ hy) h0)
  have l0 : lam = 0 := by
    have := hL F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) lam hl _ hy Φ' r1.1
    rw [key, key, orth _ hy] at this
    generalize pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) = x at this n0
    simpa [pet, n0, v0] using this
  have main : PolConst B G X om om' R Rf c := fun Ψ Ψ' h1 h2 g => by
    have hz : (Ψ, Ψ') ∈ pairs B G X R Rf := ⟨h1, h2⟩
    have := congrFun (cW.eq_zero hμ hD (cc 1 (-c) _ hz) (ci 1 (-c) _ hz) (by rw [hl _ hz _ hz, l0, zero_mul])) g
    simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun c0 => q2 (funext fun g => ?_), main⟩
  obtain ⟨Ψ', h1, h2⟩ := m1 Φ₀ q1
  rw [main Φ₀ Ψ' h1 h2 g, c0, zero_mul]; rfl

end GlobalTheory.ThK.Dbl

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.TopPolarZero.PolZero

section

@[expose] public section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEst (GrpTop EpsOf SiegelAll FinVolU)
open PositivityTheory.ThKF (Unimod ArchOp ICont PureAct CartanConj CartanMove)

theorem _root_.PositivityTheory.ThKR.polynomial_vanishing_of_compactness (p0 : SiegelWeilStd) (p2 : EisBL) (p5 : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne)
    (hN : NonZeroAn) (hF : Factor) (hM : MatchEx) (hB : ThetaBasic) (hW : WeilConv) (hD : KDecay) (hI : ICont)
    (g1 : GrpTop) (g2 : EpsOf) (g3 : SiegelAll) (g4 : FinVolU) (g5 : Unimod) : PolZero :=
  have p1 := siegelWeilAniso_of p0 frameConj finLevel stab2Cpt
  have hc := cptAll_of g1 g2 g3 g4 g5
  have l1 := boxSec_of finLevel stab2Cpt
  have l6 := pairsStable
  polZero_of hc (hermLine_of' hc l6 pairsIrr hF hN hW hB hI hM)
    (coefLine_of (swFull_of p1.1 (eisContinues_of p2 frameConj) l1) l1 dblW (hgtEx_of stab2Cpt) (hgtInt_of stab2Cpt) stab2Cpt hc l6 hM
      hB hI polSch)
    (thConst_of' locDist goodNe (PositivityTheory.SA.constOfGood p5) hF hM hB hD g1 g2 g4 g5) hN hM hB hI polSch

end GlobalTheory.ThK.Dbl
end
end
