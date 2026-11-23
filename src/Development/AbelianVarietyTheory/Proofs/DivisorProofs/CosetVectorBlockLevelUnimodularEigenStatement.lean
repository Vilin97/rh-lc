module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVanishingLevelUnitBlockMulInvStabStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSkewIdealLatticeUnitVectorUnimodularEigenStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevelStatement

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.cosetVector_conj_isTheta_some_level : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.BotPairSmall.cvec_conj_mem_TT | exact GlobalTheory.BotPairSmall.cvec_conj_mem_TT | (intros; apply GlobalTheory.BotPairSmall.cvec_conj_mem_TT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalMatrixApproxTwoAdelicModuli

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall.CongApprox

theorem approx_two_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 h𝔫 a d M m hm
  obtain ⟨n, hn, hnI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D ⊤
  have hN : 0 < Ideal.absNorm 𝔫 := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨z, hz⟩ := GlobalTheory.NormSum.VacMove.MI_approx (D := D) (cc := ⊤) top_ne_bot M (m * (n * Ideal.absNorm 𝔫))
    (Nat.mul_pos hm (Nat.mul_pos hn hN))
  refine ⟨z, GlobalTheory.NormSum.VacMove.MI.of_dvd (dvd_mul_right m _) hz, fun i l => ?_⟩
  obtain ⟨y, hy, e⟩ := hz i l
  have hny : (n : AE D) * y ∈ OhE D := hnI y hy
  have hmny : (m : AE D) * ((n : AE D) * y) ∈ OhE D := mul_mem (natCast_mem _ m) hny
  have h2 := GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔫 hmny
  have e2 : (M - z.map (inc D)) i l = -((Ideal.absNorm 𝔫 : AE D) * ((m : AE D) * ((n : AE D) * y))) := by
    rw [← neg_sub, Matrix.neg_apply, e]; push_cast; ring
  rw [e2]
  exact neg_mem h2

end GlobalTheory.BotPairSmall.CongApprox
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalMatrixApproxTwoAdelicModuliStatement

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  first | exact @GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli | exact GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli | (intros; apply GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodularStatement

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, inc D (y i l - y' i l) ∈ hatId D (D.host.conj • 𝔪)) → ∃ c : ℂ, ‖c‖ = 1 ∧ Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  first | exact @GlobalTheory.HeisTranslate.wd_unitVec_congr | exact GlobalTheory.HeisTranslate.wd_unitVec_congr | (intros; apply GlobalTheory.HeisTranslate.wd_unitVec_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerSkewConjMemThetaFunctions

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  exact GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerSkewConjMemThetaFunctionsStatement

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT | exact GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT | (intros; apply GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigen

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem cvec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho j hj
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hF := GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hmove : ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∀ y y' : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i l, (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - y'.map (inc D)) i l ∈ hatId D (D.host.conj • 𝔪)) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)) =
        c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
    intro g hg g' hg' y y' hy
    obtain ⟨m, hm0, hl⟩ := W.lift g g' y _ hF
    obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) m hm0
    rw [hl z hz1]
    obtain ⟨c1, hc1, e1⟩ := GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho z y' (fun i l => by
      have := sub_mem (hy i l) (hz2 i l)
      convert this using 1
      simp [Matrix.sub_apply, Matrix.map_apply, map_sub])
    refine ⟨c1 * c2, by rw [norm_mul, hc1, hc2, one_mul], ?_⟩
    rw [e1]
    have : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
      intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, e2, smul_smul]

  obtain ⟨k, hk, hjk⟩ := GlobalTheory.T.blockVanishingLevel_unitBlock_mul_inv_stab D 𝔪 hm hcop o a d ho j hj
  obtain ⟨y', -, hy'⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d ((unitBlock D o a d).map (inc D) *
    (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) 1 one_pos
  have hjJ : j ∈ intG D d := GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o d hj
  obtain ⟨c1, hc1, e1⟩ := hmove 1 (one_mem _) j hjJ (unitBlock D o a d) y' (fun i l => by
    have := add_mem (hjk i l) (hy' i l)
    convert this using 1
    simp [Matrix.sub_apply])
  obtain ⟨c2, hc2, e2⟩ := hmove k hk 1 (one_mem _) (unitBlock D o a d) y' (fun i l => by
    convert hy' i l using 1
    simp [Matrix.sub_apply])
  have hwd : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
    intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  set s : ℂ := ((Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) : ℂ)) with hs_def
  have hs : s ≠ 0 := by
    have h0 : (Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hn)
    have : 0 < Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) :=
      Real.sqrt_pos.2 (pow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)) _)
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hcv := GlobalTheory.T.cosetVector_conj_isTheta_some_level D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hV : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) =
      s • GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
    rw [GlobalTheory.BotPairSmall.cvec, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hVT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hV]
    obtain ⟨h1, m, hm0, h2⟩ := hcv
    exact ⟨h1.const_smul s, m, hm0, fun x hx => by rw [hwd, h2 x hx]⟩
  have hc2' : c2 ≠ 0 := by intro h; rw [h, norm_zero] at hc2; exact zero_ne_one hc2
  refine ⟨k, hk, c1 / c2, by rw [norm_div, hc1, hc2, div_one], ?_⟩
  show W.Om 1 j (s⁻¹ • _) = (c1 / c2) • W.Om k 1 (s⁻¹ • _)
  rw [W.smul _ _ _ _ hVT, W.smul _ _ _ _ hVT, e1, e2, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.BotPairSmall
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigenStatement

section

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  first | exact @GlobalTheory.BotPairSmall.cvec_eig | exact GlobalTheory.BotPairSmall.cvec_eig | (intros; apply GlobalTheory.BotPairSmall.cvec_eig <;> assumption)
end
end
