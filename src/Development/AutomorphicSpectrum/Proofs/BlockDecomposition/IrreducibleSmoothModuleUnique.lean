module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticOrthogonalVanishing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiePowerL2FactorialBoundStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticOrthogonalVanishingStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.analytic_orthogonal_vanishing : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H), (∀ k t, HasDerivAt (F k) (F (k + 1) t) t) → (∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ)) → (∀ k, inner ℂ u (F k 0) = 0) → ∀ t, inner ℂ u (F 0 t) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | exact GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | (intros; apply GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2MemStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.irreducible_cuspidal_form_l2_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → (classes W μ).topologicalClosure = H → ∀ φ : Sm E a, IsAutForm φ → ∀ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H → φ ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | exact GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubgroupOneParameterClosedEqTop

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.GenOneParam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

def packM (g : ι → Matrix n n ℂ) : Matrix n n (ι → ℂ) := Matrix.of fun i j w => g w i j

theorem packM_one : packM (1 : ι → Matrix n n ℂ) = 1 := by
  ext i j w
  by_cases h : i = j
  · subst h; simp [packM]
  · simp [packM, h]

theorem packM_mul (g h : ι → Matrix n n ℂ) : packM (g * h) = packM g * packM h := by
  ext i j w
  simp [packM, Matrix.mul_apply, Finset.sum_apply]

def packGL : (ι → GL n ℂ) →* GL n (ι → ℂ) where
  toFun g := ⟨packM fun w => (g w).val, packM fun w => (g w)⁻¹.val,
    by rw [← packM_mul, ← packM_one]; congr 1; ext1 w; simp,
    by rw [← packM_mul, ← packM_one]; congr 1; ext1 w; simp⟩
  map_one' := by
    apply Units.ext
    show packM (fun w => ((1 : ι → GL n ℂ) w).val) = 1
    rw [← packM_one]; congr 1
  map_mul' g h := by
    apply Units.ext
    show packM (fun w => ((g * h) w).val) = packM _ * packM _
    rw [← packM_mul]; congr 1

theorem packGL_val (g : ι → GL n ℂ) : (packGL g).val = packM fun w => (g w).val := rfl

theorem packGL_inv_val (g : ι → GL n ℂ) : (packGL g)⁻¹.val = packM fun w => (g w)⁻¹.val := rfl

theorem packGL_surjective : Function.Surjective (packGL : (ι → GL n ℂ) → GL n (ι → ℂ)) := by
  intro y
  refine ⟨fun w => Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : ι => ℂ) w) y, ?_⟩
  apply Units.ext
  ext i j w
  simp [packGL_val, packM]

end GlobalTheory.CompanionTheory.GenOneParam

namespace GlobalTheory.CompanionTheory.GenOneParam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

theorem packGL_mulSingle_val (w w' : ι) (g : GL n ℂ) (i j : n) :
    (packGL (Pi.mulSingle w g)).val i j w' = if w' = w then g.val i j else (1 : Matrix n n ℂ) i j := by
  by_cases h : w' = w
  · subst h; simp [packGL_val, packM]
  · simp [packGL_val, packM, h, Pi.mulSingle_eq_of_ne h]

theorem packGL_mulSingle_inv_val (w w' : ι) (g : GL n ℂ) (i j : n) :
    (packGL (Pi.mulSingle w g))⁻¹.val i j w' =
      if w' = w then g⁻¹.val i j else (1 : Matrix n n ℂ) i j := by
  by_cases h : w' = w
  · subst h; rw [packGL_inv_val]; simp [packM]
  · rw [packGL_inv_val]; simp [packM, h, Pi.mulSingle_eq_of_ne h]

theorem mem_of_family {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S)
    (w : ι) (m : ℝ → Matrix n n ℂ) (hm : Continuous m) (h0 : m 0 = 1)
    (hadd : ∀ s t, m (s + t) = m s * m t) (X₀ : n → n → ℂ)
    (hd : ∀ i j, HasDerivAt (fun t => m t i j) (X₀ i j) 0)
    (t : ℝ) (g : GL n ℂ) (hg : g.val = m t) : packGL (Pi.mulSingle w g) ∈ S := by
  let c₀ : ℝ → GL n ℂ := fun s => ⟨m s, m (-s),
    by rw [← hadd]; simp [h0], by rw [← hadd]; simp [h0]⟩
  have hc₀ : ∀ s, (c₀ s).val = m s := fun s => rfl
  have hc₀i : ∀ s, (c₀ s)⁻¹.val = m (-s) := fun s => rfl
  have hg' : c₀ t = g := Units.ext (by rw [hc₀, hg])
  have h00 : c₀ 0 = 1 := Units.ext (by rw [hc₀, h0]; rfl)
  have hadd₀ : ∀ s u, c₀ (s + u) = c₀ s * c₀ u := fun s u => Units.ext (by
    rw [Units.val_mul, hc₀, hc₀, hc₀, hadd])
  rw [← hg']
  refine hS (fun s => packGL (Pi.mulSingle w (c₀ s)))
    (fun i j w' => if w' = w then X₀ i j else 0) ?_ ?_ ?_ ?_ t
  · rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => continuous_pi fun w' => ?_
      simp only [Function.comp, packGL_mulSingle_val, hc₀]
      split_ifs
      · exact (continuous_id.matrix_elem i j).comp hm
      · exact continuous_const
    · refine continuous_matrix fun i j => continuous_pi fun w' => ?_
      simp only [packGL_mulSingle_inv_val, hc₀i]
      split_ifs
      · exact (continuous_id.matrix_elem i j).comp (hm.comp continuous_neg)
      · exact continuous_const
  · simp [h00]
  · intro s u
    simp only [hadd₀]
    rw [Pi.mulSingle_mul, map_mul]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w' => ?_
    simp only [Matrix.of_symm_apply, packGL_mulSingle_val, hc₀]
    by_cases h : w' = w
    · simpa [h] using hd i j
    · simpa [h] using hasDerivAt_const (0 : ℝ) ((1 : Matrix n n ℂ) i j)

theorem single_mem {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S)
    (w : ι) (g : GL n ℂ) : packGL (Pi.mulSingle w g) ∈ S := by
  suffices H : ∀ M : Matrix n n ℂ, M.det ≠ 0 →
      ∀ g : GL n ℂ, g.val = M → packGL (Pi.mulSingle w g) ∈ S from
    H g.val (Matrix.isUnits_det_units g).ne_zero g rfl
  intro M hM
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n ℂ, g.val = M → packGL (Pi.mulSingle w g) ∈ S) M hM ?_ ?_ ?_
  · intro D hD g hg
    have hD' : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD k (Finset.mem_univ k)
    refine mem_of_family hS w
      (fun t => Matrix.diagonal fun k => Complex.exp ((t : ℂ) * Complex.log (D k)))
      ?_ ?_ ?_ (fun i j => if i = j then Complex.log (D i) else 0) ?_ 1 g ?_
    · refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
      fun_prop
    · simp
    · intro s u
      rw [Matrix.diagonal_mul_diagonal']
      congr 1; ext k
      rw [← Complex.exp_add]; push_cast; ring_nf
    · intro i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq, if_true]
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.log (D i)) (Complex.log (D i)) 0 := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (Complex.log (D i))
        simpa using h1.cexp
      · simpa [h, Matrix.diagonal_apply_ne _ h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · rw [hg]; congr 1; ext k
      simp [Complex.exp_log (hD' k)]
  · intro τ g hg
    refine mem_of_family hS w (fun t => Matrix.transvection τ.i τ.j ((t : ℂ) * τ.c))
      ?_ ?_ ?_ (fun a b => (Matrix.single τ.i τ.j τ.c : Matrix n n ℂ) a b) ?_ 1 g ?_
    · unfold Matrix.transvection
      refine continuous_const.add ?_
      refine continuous_matrix fun a b => ?_
      simp only [Matrix.single_apply]
      split_ifs
      · fun_prop
      · exact continuous_const
    · simp
    · intro s u
      rw [Matrix.transvection_mul_transvection_same _ _ τ.hij]
      congr 1; push_cast; ring
    · intro a b
      unfold Matrix.transvection
      simp only [Matrix.add_apply, Matrix.single_apply]
      split_ifs
      · have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * τ.c) τ.c 0 := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const τ.c
        exact h1.const_add _
      · exact hasDerivAt_const (0 : ℝ) _ |>.add (hasDerivAt_const (0 : ℝ) (0 : ℂ)) |>.congr_deriv (by simp)
    · rw [hg]; simp [Matrix.TransvectionStruct.toMatrix]
  · intro A B hA hB PA PB g hg
    have : g = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
        Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext (by rw [hg]; rfl)
    rw [this, Pi.mulSingle_mul, map_mul]
    exact S.mul_mem (PA _ rfl) (PB _ rfl)

theorem eq_top_of_oneParam {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S) : S = ⊤ := by
  have hle : Subgroup.pi Set.univ (fun _ : ι => (⊤ : Subgroup (GL n ℂ))) ≤ S.comap packGL := by
    rw [Subgroup.pi_le_iff]
    rintro w _ ⟨g, -, rfl⟩
    exact single_mem hS w g
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨g, rfl⟩ := packGL_surjective y
  exact hle (by simp [Subgroup.mem_pi])

theorem eq_top_of_oneParam_Cinf : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Subgroup (GL (Fin a) (Cinf E))), (∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : GlobalTheory.CuspRep.Lie E a), Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 → ∀ t, c t ∈ S) → S = ⊤ := by
  intro E _ _ a S hS
  classical
  exact eq_top_of_oneParam (ι := InfinitePlace E) (n := Fin a) hS

end GlobalTheory.CompanionTheory.GenOneParam
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubgroupOneParameterClosedEqTopStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.subgroup_one_parameter_closed_eq_top : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Subgroup (GL (Fin a) (Cinf E))), (∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : GlobalTheory.CuspRep.Lie E a), Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 → ∀ t, c t ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | exact GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | (intros; apply GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUnique

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CuspIrred

open scoped InnerProductSpace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem continuous_infGL' : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem map_closure_le {C S : Submodule ℂ (L2 (latticeGL E a) μ)} (hC : C = S.topologicalClosure)
    (T : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) (h : ∀ F ∈ S, T F ∈ C) {v : L2 (latticeGL E a) μ}
    (hv : v ∈ C) : T v ∈ C := by
  have hcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := hC ▸ Submodule.isClosed_topologicalClosure _
  have hle : S.topologicalClosure ≤ C.comap (T : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
    Submodule.topologicalClosure_minimal _ h (hcl.preimage T.continuous)
  exact hle (hC ▸ hv)

theorem R_curve_mem {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) {c : ℝ → GL (Fin a) (Cinf E)} {X : GlobalTheory.CuspRep.Lie E a}
    (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) {φ : Sm E a} (hφ : φ ∈ W) (h : MemL2Quotient (latticeGL E a) μ φ.1) (t : ℝ) :
    R (latticeGL E a) μ (infGL E a (c t)) h.toL2 ∈ (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hCcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace C := hCcl.completeSpace_coe
  let ψ : ℕ → Sm E a := fun k => ((lie E a X) ^ k) φ
  have hψ0 : ψ 0 = φ := rfl
  have hψs : ∀ k, ψ (k + 1) = lie E a X (ψ k) := fun k => by
    simp only [ψ, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, ψ k ∈ W := fun k => by
    induction k with
    | zero => exact hφ
    | succ k ih => rw [hψs]; exact hs (.lie X) _ ih
  have hM : ∀ k, MemL2Quotient (latticeGL E a) μ (ψ k).1 := fun k => (hW _ (hmem k)).2
  have hcont : ∀ k, Continuous (ψ k).1 := fun k => ContAut.continuous_of_isOpen_stab E a _ (hW _ (hmem k)).1.level
  let F : ℕ → ℝ → L2 (latticeGL E a) μ := fun k t => R (latticeGL E a) μ (infGL E a (c t)) (hM k).toL2
  obtain ⟨M, B, hb⟩ := GlobalTheory.T.lie_power_l2_factorial_bound E a μ W hs hW φ hφ X
  have hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t := fun k t =>
    GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ (ψ k).1 (ψ (k + 1)).1 (hM k) (hM (k + 1)) (fun t => infGL E a (c t))
      (hcont k) (hcont (k + 1)) (continuous_infGL'.comp hc) (by simp [h0]) (fun s t => by simp [hadd])
      (fun g => by
        have := hasDerivAt_curve (ψ k) g c X h0 hX
        rw [hψs]
        exact this) t
  have hn : ∀ k t, ‖F k t‖ ≤ M * B ^ k * (k.factorial : ℝ) := fun k t => (norm_R _ _).trans_le (hb k (hM k))
  have hF0 : ∀ k, F k 0 ∈ C := fun k => by
    have : F k 0 = (hM k).toL2 := by simp [F, h0]
    rw [this]
    exact Submodule.le_topologicalClosure _ (toL2_mem_classes (hmem k) (hM k))
  have hperp : F 0 t ∈ Cᗮᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu =>
    GlobalTheory.T.analytic_orthogonal_vanishing _ F M B u hd hn (fun k => (Submodule.mem_orthogonal' _ _).1 hu _ (hF0 k)) t
  rw [Submodule.orthogonal_orthogonal] at hperp
  have e : (hM 0).toL2 = h.toL2 := rfl
  exact e ▸ hperp

theorem isSubrep_closure {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) :
    IsSubrep (R (latticeGL E a) μ) (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hcls : ∀ F ∈ classes W μ, ∃ φ ∈ W, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, F = h.toL2 := fun F hF => by
    obtain ⟨φ, hφ, e⟩ := mem_classes.1 hF
    exact ⟨φ, hφ, (hW φ hφ).2, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (hW φ hφ).2.lift_toL2_ae_eq.symm)⟩
  have hfin : ∀ k, ∀ v ∈ C, R (latticeGL E a) μ (finGL E a k) v ∈ C := fun k v hv =>
    map_closure_le hCdef _ (fun F hF => Submodule.le_topologicalClosure _
      (R_mem_classes (fun φ hφ => hs (.fin k) φ hφ) hF)) hv
  let S : Subgroup (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (∀ v ∈ C, R (latticeGL E a) μ (infGL E a y) v ∈ C) ∧
        ∀ v ∈ C, R (latticeGL E a) μ (infGL E a y⁻¹) v ∈ C}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => ⟨fun v hv => by
          rw [map_mul, map_mul]; exact hx.1 _ (hy.1 v hv), fun v hv => by
          rw [_root_.mul_inv_rev, map_mul, map_mul]; exact hy.2 _ (hx.2 v hv)⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩ }
  have hS : S = ⊤ := GlobalTheory.T.subgroup_one_parameter_closed_eq_top E a S fun c X hc h0 hadd hX t => by
    have key : ∀ t, ∀ v ∈ C, R (latticeGL E a) μ (infGL E a (c t)) v ∈ C := fun t v hv =>
      map_closure_le hCdef _ (fun F hF => by
        obtain ⟨φ, hφ, h, rfl⟩ := hcls F hF
        exact R_curve_mem hs hW hc h0 hadd hX hφ h t) hv
    have hinv : (c t)⁻¹ = c (-t) := inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
    exact ⟨key t, by rw [show (c t)⁻¹ = c (-t) from hinv]; exact key (-t)⟩
  refine ⟨Submodule.isClosed_topologicalClosure _, fun g v hv => ?_⟩
  have hy : GeneralLinearGroup.map (pInf E) g ∈ S := hS ▸ Subgroup.mem_top _
  rw [← infGL_mul_finGL g, map_mul]
  exact hy.1 _ (hfin _ v hv)

theorem irred_module : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → W ≠ ⊥ → (∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → ∀ φ : Sm E a, (IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → φ ∈ W := by
  rintro E _ _ _ a μ _ _ H hH hi W hs hne hW φ ⟨hφ, -, h, hh⟩
  have hW' : ∀ ψ ∈ W, IsAutForm ψ ∧ MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ =>
    ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2.choose⟩
  have hsub := isSubrep_closure (μ := μ) hs hW'
  have hle : (classes W μ).topologicalClosure ≤ H := by
    refine Submodule.topologicalClosure_minimal _ (fun F hF => ?_) hi.1.1
    obtain ⟨ψ, hψ, e⟩ := mem_classes.1 hF
    obtain ⟨h', hh'⟩ := (hW ψ hψ).2.2
    rwa [show F = h'.toL2 from l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h'.lift_toL2_ae_eq.symm)]
  have hcl : (classes W μ).topologicalClosure = H := by
    refine (hi.2.2 _ hle hsub).resolve_left fun h0 => ?_
    obtain ⟨ψ, hψ, hψ0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨h', -⟩ := (hW ψ hψ).2.2
    refine toL2_ne_zero h' (ContAut.continuous_of_isOpen_stab E a ψ (hW ψ hψ).1.1.level)
      (fun e => hψ0 (Subtype.ext e)) ?_
    have : h'.toL2 ∈ (classes W μ).topologicalClosure :=
      Submodule.le_topologicalClosure _ (toL2_mem_classes hψ h')
    rw [h0] at this
    exact this
  exact GlobalTheory.T.irreducible_cuspidal_form_l2_mem E a μ H hH hi W hs (fun ψ hψ => ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2⟩) hcl φ hφ.1 h hh

end GlobalTheory.CompanionTheory.CuspIrred
end
end
