module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.NormOne

variable {p : ℕ} [Fact p.Prime]

theorem norm_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ ≤ 1 := by
  rw [(X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_sigma_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
  rw [hy]
  exact norm_alg_le X E v _

theorem norm_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (u : (X.G.P.W v)ˣ) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ = 1 ∧
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ = 1 := by
  have h1 : ((u : X.G.P.W v) * ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := Units.mul_inv u
  have e1 : ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ *
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, norm_one]
  have e2 : ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ *
      ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, map_one, norm_one]
  have a1 := norm_alg_le X E v (u : X.G.P.W v)
  have a2 := norm_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have b1 := norm_sigma_alg_le X E v (u : X.G.P.W v)
  have b2 := norm_sigma_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have n1 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))
  have n2 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))
  have n3 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))))
  have n4 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))))
  constructor <;> nlinarith

theorem norm_sigma_alg (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ =
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (X.G.P.setting v).p_unif
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, (norm_unit X E v u).1, (norm_unit X E v u).2]

theorem norm_sigma (X : Sys p) (E : CEmb X.G) (v : X.Pl) (y : X.G.P.Qq v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v y))‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) y
  simp only [map_div₀, norm_div, norm_sigma_alg]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.Qq v) :
    ‖twG X E v s y‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  simp only [twG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  generalize s.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((X.G.P.σ v) ^ (n + 1)) y = X.G.P.σ v (((X.G.P.σ v) ^ n) y) := by rw [pow_succ']; rfl
    rw [e, norm_sigma, ih]

theorem prod_parity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if s.val % 2 = 1 then b else a) = (a * b) ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [Fin.prod_univ_eq_prod_range (fun i => if i % 2 = 1 then b else a) (m + m)]
  have : m + m = 2 * m := by ring
  rw [this, Nat.mul_div_cancel_left m (by norm_num)]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h0 : ¬ (2 * m) % 2 = 1 := by omega
    simp only [h1, h0, if_true, if_false]
    rw [mul_assoc]

theorem prod_parity_pos {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if IsOddPos s then b else a) = (a * b) ^ (n / 2) := by
  rw [← prod_parity a b n hn]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1
  · rw [if_pos h, if_pos (show IsOddPos s from h)]
  · rw [if_neg h, if_neg (show ¬ IsOddPos s from h)]

end GlobalTheory.TwU.NormOne

namespace GlobalTheory.TwU.NormOne

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have h : IsIntegral ℚ (TaylorLogMetric.embT D τ x) := (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom
  exact mem_algebraicClosure_iff.2 h.isAlgebraic

end GlobalTheory.TwU.NormOne


open GlobalTheory.TwU.NormOne in
theorem GlobalTheory.TwV.prod_embT_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  intro D _ hT _ _ _ _ _ _ u _ w hg _ _ H X _ std _ J S hPos ι hι z hz
  have hl : ∀ τ, ι (TaylorLogMetric.embT D τ z) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D τ z) := by
    intro τ
    rw [TaylorLogMetric.lamC, dite_eq_left (embT_mem_qbar D τ z)]
    exact hι ⟨_, embT_mem_qbar D τ z⟩
  rw [map_prod, norm_prod]
  simp only [hl]
  rw [← Fintype.prod_equiv (hT.gat_pos u w hg) (fun σ => ‖TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg σ) z)‖) _ (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  have hP : ∀ v s x, TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) =
      twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj x else x)) := hPos
  refine Finset.prod_eq_one fun v _ => ?_
  have hs : ∀ s : Fin ((sysS H X std).G.P.n' v),
      ‖twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj z else z))‖ =
        if IsOddPos s then ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v (D.host.conj z)))‖
        else ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v z))‖ := by
    intro s
    split_ifs <;> exact norm_twG _ _ _ _ _
  simp only [hP]
  refine (Finset.prod_congr rfl fun s _ => hs s).trans ?_
  rw [prod_parity_pos _ _ _ ((sysS H X std).G.P.setting v).even, ← norm_mul, ← map_mul, ← map_mul, ← map_mul, hz,
    map_one, map_one, map_one, norm_one, one_pow]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  first | exact @GlobalTheory.TwV.prod_embT_norm_one | exact GlobalTheory.TwV.prod_embT_norm_one | (intros; apply GlobalTheory.TwV.prod_embT_norm_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.ScaleUnit

theorem norm_ltC_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  obtain ⟨-, hAt, -⟩ := S.curve
  obtain ⟨h1, h2, h3, hLam, hOk⟩ := hAt
  have hU : GL3Theta.IsModelU S.g.lam (TaylorLogMetric.lamOf D t.cc t.δ) S.g.C := hLam ▸ hOk.1
  have hu := (GlobalTheory.UnitModel.modelEx_holds D _ S.g.lam t.cc t.δ h1 h2 h3).2.2 S.g.C hU
  unfold ltC
  rw [norm_inv, norm_mul, hu, norm_wToC_unit, mul_one, inv_one]

end GlobalTheory.TwU.ScaleUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_site_coordinate_scale_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  first | exact @GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one | exact GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one | (intros; apply GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_lb {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (β : S.Ch) (T : GlobalTheory.TwU.StepCharts C' i hi) (hT : T = castSt h S) :
    ∃ β' : T.Ch, (T.K β').lev.Lb = (S.K β).lev.Lb := by
  subst hT
  subst h
  exact ⟨β, rfl⟩

theorem uB_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a τ
  have hU := GlobalTheory.T.local_space_gram_transform S hPos ι hι j hj
  have hO := (bAt_orth_lev S j hj a).1
  have e : (uB J j hj a).1.det = (J.A.crd j hj).1.det * (bAt J j hj a).1.det := by
    simp [uB, Matrix.det_mul]
  rw [e]
  cases j with
  | zero =>
    obtain ⟨c⟩ := Formalism.MainNotions.G.KAat.cl_nonempty J.one a
    refine hU ((J.St 0 hj).chOf (J.e0 c)) (bAt J 0 hj a) hO (fun v => ?_) τ
    rw [(J.lev0 _).1]
    exact J.lb0 v
  | succ j =>
    obtain ⟨β, hβ⟩ := castSt_lb (X.onCh j hj) (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) ((I.at' j hj).st.eC.symm a).1 _ (J.st j hj)
    refine hU β (bAt J (j + 1) hj a) hO (fun v => ?_) τ
    rw [hβ]
    have h1 := J.lbB j hj ((I.at' j hj).st.eC.symm a).1 v
    rw [J.iw j hj _ v] at h1
    exact h1

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthonormalChartBasis_det_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelA.uB_det_unit | exact GlobalTheory.TwV.DelA.uB_det_unit | (intros; apply GlobalTheory.TwV.DelA.uB_det_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem cKs_unit_indep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'
  have hB := GlobalTheory.T.orthonormalChartBasis_det_norm_one S hPos ι hι
  have hG := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι
  have hD := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S
  have hL := GlobalTheory.T.norm_site_coordinate_scale_eq_one S
  have hN := GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one S hPos ι hι
  have hBas := bAt_orth_lev S
  beta_reduce at hD hL hBas
  have hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ),
      (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1 := by
    intro n M e hM
    unfold dPow
    rw [map_prod, norm_prod]
    exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])
  have hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1 := by
    intro k hk c
    unfold dPow
    rw [Finset.prod_zpow, map_zpow₀, norm_zpow]
    rw [show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]
    rw [hN _ (hD k hk).1, one_zpow]
  have hsg : ∀ n, ‖ι (sgRev n)‖ = 1 := by
    intro n
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]
  have hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    have h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1 := by
      unfold sgO
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one (fun τ _ => ?_)
      split_ifs
      · simp [hsg]
      · simp
    have h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1 := by
      rw [map_prod, norm_prod]
      exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])
    unfold cOp
    rw [map_mul, norm_mul, h1, h2, one_mul]
  have hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1 := by
    intro b
    unfold kS
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1 := by
    intro b
    unfold kT
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkSc : ∀ b : Lv.comp j,
      ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    intro b
    rw [map_mul, norm_mul, hkS, hcOp, one_mul]
  have hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a := by
    intro b
    simp only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]
  have hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a' := by
    intro b
    simp only [kT, uB, (hBas (j + 1) hj a').2 b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cKs
    rw [norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]
  · intro h
    have h1 := hkSc a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  · intro b b'
    unfold cKs
    rw [hkSeq b, hkTeq b']

end GlobalTheory.TwV.DelA
end
end
