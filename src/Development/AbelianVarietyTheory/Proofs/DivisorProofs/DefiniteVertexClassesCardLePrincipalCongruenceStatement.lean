module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRationalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEq

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

theorem exists_finG_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram →
    ∃ g : GfC V, finG V g = M := by
  intro D V M hM
  obtain ⟨g0, hg0⟩ := GlobalTheory.FunObj.UA_le_range_finE V hM
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g0) (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g0)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  rw [← hg0]
  change Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g0)
  rw [k2]

end GlobalTheory.FrameTransport

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram → ∃ g : GfC V, finG V g = M := by
  first | exact @GlobalTheory.FrameTransport.exists_finG_eq | exact GlobalTheory.FrameTransport.exists_finG_eq | (intros; apply GlobalTheory.FrameTransport.exists_finG_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  first | exact @GlobalTheory.FrameTransport.frConj_mem_UA | exact GlobalTheory.FrameTransport.frConj_mem_UA | (intros; apply GlobalTheory.FrameTransport.frConj_mem_UA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongrStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.FrameTransport.Cong.conj_mem_congLev | exact GlobalTheory.FrameTransport.Cong.conj_mem_congLev | (intros; apply GlobalTheory.FrameTransport.Cong.conj_mem_congLev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruence

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport


open GlobalTheory.FrameTransport in
theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
    (DoubleCoset.out_eq'
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruenceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

theorem _root_.GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  first | exact @GlobalTheory.FrameTransport.finCl_card_le | exact GlobalTheory.FrameTransport.finCl_card_le | (intros; apply GlobalTheory.FrameTransport.finCl_card_le <;> assumption)
end
end
