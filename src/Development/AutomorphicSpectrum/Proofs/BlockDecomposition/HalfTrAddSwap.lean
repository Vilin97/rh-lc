module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) (AE F E), M.map (cA σ) = M.map (sigR (AF F) σ) := fun M => by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  ext g
  change (g.1)ᵀ * incM F J * (g.1).map (cA σ) = incM F J ↔ cT (sigR (AF F) σ) g.1 * JR (AF F) Jᵀ * g.1 = JR (AF F) Jᵀ
  rw [hc, hJ, cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ofGAd : GAd σ Jᵀ ≃* UA σ J := MulEquiv.subgroupCongr (UG_eq_HR σ J).symm

theorem mat_ofGAd (g : GAd σ Jᵀ) : mat (ofGAd σ J g) = (matHom (AF F) σ Jᵀ g).1 := rfl

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {g | ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x}
  one_mem' := ⟨1, by simp [mat, Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show (mat g * mat h) *ᵥ incV F x = _
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have e : mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at e
    calc mat g⁻¹ *ᵥ incV F x = ((a⁻¹ : (AE F E)ˣ) : AE F E) • ((a : AE F E) • mat g⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e]

theorem mem_lineStab {x : Fin n → E} {g : UA σ J} :
    g ∈ lineStab σ J x ↔ ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x := Iff.rfl

end GlobalTheory.IwLine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

end GlobalTheory.SWLink

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Weyl

variable {D : D7} {n : ℕ}

theorem mat_inv_eq (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) : mat g⁻¹ = blk4 0 (-1) 1 0 := by
  have h : blk4 (0 : Mx D n n) (-1) 1 0 * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simpa using block_matrix_one (n := n) (R := AE D)
  calc mat g⁻¹ = (blk4 (0 : Mx D n n) (-1) 1 0 * mat g) * mat g⁻¹ := by rw [h, Matrix.one_mul]
    _ = blk4 0 (-1) 1 0 := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem inner_add_left (V : HSp D) (a b c : Mx D V.rank n) :
    inner V (a + b) c = inner V a c + inner V b c := by
  simp only [GlobalTheory.StdUnn.inner, adj_add, Matrix.add_mul]

theorem inner_add_right (V : HSp D) (a b c : Mx D V.rank n) :
    inner V a (b + c) = inner V a b + inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add]

theorem inner_neg_left (V : HSp D) (a c : Mx D V.rank n) : inner V (-a) c = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, adj_neg, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) (a c : Mx D V.rank n) : inner V a (-c) = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add _ a b

theorem trA_neg (a : AE D) : trA (-a) = -trA a := map_neg _ a

theorem halfTr_add_swap (V : HSp D) (a b : Mx D V.rank n) :
    halfTr (Matrix.trace (inner V a b)) + halfTr (Matrix.trace (inner V b a)) =
      trA (Matrix.trace (inner V a b)) := by
  have h : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  rw [halfTr, halfTr, ← GlobalTheory.SWLink.trA_inner_comm V a b, ← add_mul, h, one_mul]

theorem phase (V : HSp D) (t x y z : Mx D V.rank n) :
    (trA (Matrix.trace (inner V (t + -x) y)) + halfTr (Matrix.trace (inner V x y))) +
        trA (Matrix.trace (inner V z (t + -x))) =
      (trA (Matrix.trace (inner V z (-x))) + halfTr (Matrix.trace (inner V y (-x)))) +
        trA (Matrix.trace (inner V (z + y) t)) := by
  have h := halfTr_add_swap V x y
  have c := GlobalTheory.SWLink.trA_inner_comm V t y
  have hn : halfTr (Matrix.trace (inner V y (-x))) = -halfTr (Matrix.trace (inner V y x)) := by
    rw [inner_neg_right, Matrix.trace_neg, halfTr, halfTr, trA_neg, mul_neg]
  rw [hn]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, Matrix.trace_add, Matrix.trace_neg,
    trA_add, trA_neg]
  rw [c, ← h]
  abel

end GlobalTheory.CompanionTheory.EisCovar.Weyl

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → μ.IsAddHaarMeasure → ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hω hμ g hg v Φ Ψ hΨ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = yPart v := by
    rw [Weyl.mat_inv_eq g hg, x_part_mul_block]; simp
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = -xPart v := by
    rw [Weyl.mat_inv_eq g hg, y_part_mul_block]; simp
  funext z
  rw [hω.weyl g hg Ψ z]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, hω.weyl g hg Φ (z + yPart v), ← integral_const_mul,
    ← integral_add_right_eq_self (μ := μ) (fun t => Ψ.1 t * ψ (trA (Matrix.trace (inner V z t)))) (-xPart v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have e := Weyl.phase V t (xPart v) (yPart v) z
  have e2 := congrArg ψ e
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (_ + _)] at e2
  simp only [hΨ, PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, neg_add_cancel_right]
  linear_combination (Φ.1 t) * e2

end GlobalTheory.CompanionTheory.EisCovar
end
end
end
