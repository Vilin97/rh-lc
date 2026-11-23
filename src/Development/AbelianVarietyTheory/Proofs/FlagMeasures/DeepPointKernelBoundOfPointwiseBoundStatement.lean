module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKTypeStatement
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CuspidalFrames
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKTypeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwiners

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrameOneType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

theorem cuspidal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  intro B d h hd hS _ hgap hl hb hfin
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, hP⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨hproj, hfix, hex, -, -⟩ := hP Rφ hR
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨T, hT, hn, ho, hsp⟩ := GlobalTheory.IntertwinerFrame.exists_orthonormal_frame B d hd hfin hle
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨Rφ, hR, T, hT, fun i => hle (hT i), hn, ho, hsp, fun i u => ?_, fun i u k hk => ?_, ?_, ?_⟩
  · have hw' : T i (B.tens B.w) ∈ S := by
      rw [hSm, ← hfix _ (hT i)]
      exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hd hS hgap hl hb hfin Rφ hR _).2
    have hcl : IsClosed ((S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage (T i).continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle (hT i) g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T i (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT i
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)
  · exact ⟨fun i => by rw [hn, hw], fun i j hij => ho i j hij _ _⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, hfix _ (hT i)⟩
    · rintro _ ⟨z, rfl⟩
      have hz : Rφ (Rφ z) = Rφ z :=
        congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C z) hproj.1
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ hz
      rw [← hsp] at hA
      have := Submodule.mem_map_of_mem
        (f := (ContinuousLinearMap.apply ℂ (B.I.L2 B.μf B.fund) (B.tens B.w)).toLinearMap) hA
      rw [Submodule.map_span, ← Set.range_comp] at this
      show Rφ z ∈ _
      rw [← hAw]
      exact this

end GlobalTheory.Dec.CuspFrameOneType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwinersStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  first | exact @GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | exact GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | (intros; apply GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.KerDiagBasisIndep

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem kerDiag_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y : Fin D → H) (hy : Orthonormal ℂ y) (v : H) (hv : v ∈ Submodule.span ℂ (Set.range y)) :
    v = ∑ i, ⟪y i, v⟫_ℂ • y i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy.inner_right_fintype]

theorem kerDiag_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y y' : Fin D → H) (hy : Orthonormal ℂ y) (hy' : Orthonormal ℂ y') (a b : Fin D → ℂ)
    (hb : ∀ j, b j = ∑ i, ⟪y i, y' j⟫_ℂ * a i) :
    ∑ j, ‖b j‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu
  have h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖ := by
    intro j
    rw [norm_inner_symm, hb, hu, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_conj, mul_comm]
  have h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    have h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hu, hy.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [inner_self_eq_norm_sq_to_K] at h3
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← h3, Complex.ofReal_pow]
    rfl
  simp only [h1]
  rw [← h2]
  exact hy'.sum_inner_products_le u

theorem kerDiag_add_rep (B : RowsAut) (F F' : B.I.L2 B.μf B.fund) (f f' : B.I.GA → ℂ) (c : ℂ)
    (h : IsContRep B F f) (h' : IsContRep B F' f') :
    IsContRep B (F + c • F') (fun x => f x + c * f' x) := by
  refine ⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩
  · simp only [h.2.1 γ hγ x, h'.2.1 γ hγ x]
  · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem kerDiag_sum_rep (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (f : ι → B.I.GA → ℂ) (c : ι → ℂ) (F : B.I.L2 B.μf B.fund) (g : B.I.GA → ℂ)
    (hg : IsContRep B F g) (h : ∀ i, IsContRep B (y i) (f i)) :
    IsContRep B (F + ∑ i ∈ s, c i • y i) (fun x => g x + ∑ i ∈ s, c i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have := kerDiag_add_rep B _ _ _ _ (c a) ih (h a)
    simp only [Finset.sum_insert ha]
    convert this using 1
    · abel
    · funext x; ring

theorem kerDiag_vals (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund)
    (f f' : Fin D → B.I.GA → ℂ) (hy : Orthonormal ℂ y)
    (hs : Submodule.span ℂ (Set.range y') ≤ Submodule.span ℂ (Set.range y))
    (h : ∀ i, IsContRep B (y i) (f i)) (h' : ∀ i, IsContRep B (y' i) (f' i)) (j : Fin D)
    (x : B.I.GA) : f' j x = ∑ i, ⟪y i, y' j⟫_ℂ * f i x := by
  have e := kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))
  have h1 := kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h
  rw [← e] at h1
  have h2 := kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)
  rw [one_smul] at h2
  have h3 := congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x
  simp only [one_mul, add_right_inj] at h3
  exact h3.symm

theorem kerDiag_basis_indep : ∀ (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund) (f f' : Fin D → B.I.GA → ℂ), Orthonormal ℂ y → Orthonormal ℂ y' → Submodule.span ℂ (Set.range y) = Submodule.span ℂ (Set.range y') → (∀ i, IsContRep B (y i) (f i) ∧ IsContRep B (y' i) (f' i)) → ∀ x, ∑ i, ‖f i x‖ ^ 2 = ∑ i, ‖f' i x‖ ^ 2 := by
  intro B D y y' f f' hy hy' hs h x
  apply le_antisymm
  · exact kerDiag_le y' y hy' hy _ _ fun j =>
      kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x
  · exact kerDiag_le y y' hy hy' _ _ fun j =>
      kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x

end GlobalTheory.Dec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypothesesStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.isKTypeOf_lowK_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  first | exact @GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | exact GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | (intros; apply GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBound

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepKernel

theorem deep_kernel_bound_of_ptBound : PtBound →
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  intro hP hF Cg n₀ B d p q b c x _ hn hq hC hc hx
  obtain ⟨-, -, -, -, -, hqn, hrk, hmin, -, -, -, -, h, -, hgap, h40, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn hC
  have hD : IsDSData B d := hC.1
  have hg : 1 ≤ B.g := hC.2.2.2.2.2.2.2.2.2.1
  have hS := GlobalTheory.T.isKTypeOf_lowK_of_countHyp B Cg n₀ d p q b hn hC
  have hfin := hF B Cg n₀ d p q b hn hC
  have hloc : LocDec B h := (hP B d p q h hD hC.2.1 hgap (by rw [hmin]; exact h120)).2.2.2.2.2.2
  obtain ⟨Rφ, hR, T, -, hT2, hT3, -, -, hT6, hT7, hT8, hT9⟩ :=
    GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners B d h hD hS hg (fun v => by rw [hrk v]; exact h120) hloc h40 hfin
  choose Fr hFr using fun i => GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType B d hD hS hg (T i) (hT2 i) (hT7 i)
  obtain ⟨y, Fc, hy, hsp, hFc, hk, -⟩ := GlobalTheory.KernelExpansion.kernelB B d h hD (by omega) hloc h32 hfin Rφ hR
  have hw := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hD 0).1
  have e := GlobalTheory.Dec.kerDiag_basis_indep B B.D y (fun i => T i (B.tens B.w)) Fc (fun i => Fr i (B.tens B.w))
    hy hT8 (hsp.trans hT9.symm) (fun i => ⟨hFc i, (hFr i 0 _ hw).1⟩) x
  have e2 : (kern B.I (phe B d) x x).re = ‖vv B Fr (B.tens B.w) x‖ ^ 2 := by
    rw [hk, EuclideanSpace.norm_sq_eq, Complex.re_sum]
    simp only [vv]
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e2]
  exact GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily B Cg n₀ d p q b c x B.D T Fr hn hq hC hc hx hFr hT3 hT6

end GlobalTheory.DeepKernel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepPointKernelBound_of_pointwiseBound : PtBound → (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  first | exact @GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound | exact GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound | (intros; apply GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound <;> assumption)
end
end
