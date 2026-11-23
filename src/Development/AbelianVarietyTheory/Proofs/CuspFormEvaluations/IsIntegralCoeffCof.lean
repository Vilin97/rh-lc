module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsHarmonicProdOfDisjointColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremalStatement
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrInPsiConjugate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingMinorProductHarmonicGenerates
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemNabStdOfDetMulIntegral
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemOfForallLocP
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.FrameRead

open GlobalTheory.Harm Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)}

noncomputable def IsEnum.idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : Ix :=
  ((h.2 t.1).1 t.2).choose


omit [Fintype Ix] in
theorem IsEnum.pl_idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : pl (h.idx t) = t.1 :=
  ((h.2 t.1).1 t.2).choose_spec

theorem rename_letAct (h : IsEnum H pl) {K : Type} [Field K] (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K g P) =
      colSubst (fun t => (g (h.idx t) : Matrix (Fin n) (Fin n) K)ᵀ)
        (fun t => (((g (h.idx t))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)
        (rename (thetaLetterEquiv Dw n) P) := by
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) =
    (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · have h1 : ∃ t, pl t = τ := (h.2 τ).1 hτ

    rw [dite_eq_left h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]
    rfl
  · have h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun h1 =>
      ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ
    have h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ :=
      ⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩
    have h3 : h2.choose = h.idx ⟨τ, hτ⟩ := h.1 (by
      rw [h.pl_idx]
      exact (ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)

    rw [dite_eq_right h1, dite_eq_left h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply,
    map_sum, h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]
    rfl

theorem letAct_mul_one_mem_HHa :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (K : Type) [Field K] [CharZero K] (a : (E →+* ℂ) × ℕ → ℕ), (∀ g g' : Ix → GL (Fin n) K, letAct Dw pl K (g * g') = (letAct Dw pl K g).comp (letAct Dw pl K g')) ∧ letAct Dw pl K (1 : Ix → GL (Fin n) K) = AlgHom.id K _ ∧ ∀ (g : Ix → GL (Fin n) K), ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), letAct Dw pl K g P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw n Ix _ pl h _ K _ _ a
  have hinj := rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective
  refine ⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩
  · rw [AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h,
      ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
  · rw [rename_letAct Dw h]
    simp only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]
  · have key := mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K)
      (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))
    obtain ⟨h₁, h₂, h₃⟩ := (key P).1 hP
    refine (key _).2 ?_
    have e := rename_letAct Dw h g P
    unfold thetaLetterEquiv at e
    rw [e]
    exact ⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one],
      fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r),
      fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩

end GlobalTheory.FrameRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HodgeWeightDominanceCondition

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Classical Matrix

theorem det_gen_ne_zero {K : Type} [Field K] {Ix : Type} {n : ℕ} (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)) h
  rw [RingHom.map_det] at h2
  have : (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)).mapMatrix
      (gen K n t) = 1 := by
    ext1 i j
    simp [gen]
  rw [this] at h2
  simp at h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero t)

theorem cof_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first
  | exact @_root_.GlobalTheory.WeightOrderLemmas.main
  | exact _root_.GlobalTheory.WeightOrderLemmas.main
  | (apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightOrderLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightOrderLemmas.main ..)

end GlobalTheory.FrameRead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HodgeWeightDominanceConditionStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

theorem _root_.GlobalTheory.T.hodge_weight_dominance_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first | exact @GlobalTheory.FrameRead.cof_image | exact GlobalTheory.FrameRead.cof_image | (intros; apply GlobalTheory.FrameRead.cof_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrConjugateUnit

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem inPsi_or_conjugate_unit {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  first
  | exact @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | (apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate ..)

theorem gaStar_conj_eq_letAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (ga : Matrix (Fin n) (Fin n) E) (h : IsUnit ga.det), ga.conjTranspose * ga = 1 → gaStar (Dw := Dw) c (ga.map (IsCMField.complexConj E)) = letAct Dw pl c.F (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) := by
  intro E _ _ _ H Dw n Ix _ pl hpl _ l c ga h hU
  have hval : ((Matrix.nonsingInvUnit ga h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga := rfl
  have hinv : (((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      = ga.conjTranspose := by
    rw [Matrix.coe_units_inv, hval]
    exact Matrix.inv_eq_left_inv hU
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, b⟩
  simp only [Formalism.L2.Pj.gaStar, letAct, aeval_X, letB]
  split_ifs with h1 h2
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h1.choose :
        Matrix (Fin n) (Fin n) c.F) j b = embF c (pl h1.choose)
          ((((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b j) := rfl
    rw [e, hinv, h1.choose_spec]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h2.choose)⁻¹ : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F) b j = embF c (pl h2.choose) (ga j b) := rfl
    rw [e]
    apply Subtype.ext
    change τ (IsCMField.complexConj E (ga j b)) = pl h2.choose (ga j b)
    have hs := h2.choose_spec
    generalize h2.choose = t at hs ⊢
    subst hs
    rw [IsCMField.complexEmbedding_complexConj]
    simp
  · exfalso
    rcases inPsi_or_conjugate_unit H τ with h3 | h3
    · exact h1 ((hpl.2 τ).1 h3)
    · obtain ⟨t, ht⟩ := (hpl.2 _).1 h3
      exact h2 ⟨t, by rw [ht]; ext x; simp⟩

end GlobalTheory.FrameRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameRead.CoefMap

def harmSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  add_mem' := by
    rintro P Q ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨add_mem h1 h1', fun σ i i' h t => by rw [map_add (f := _), h2 σ i i' h t, h2' σ i i' h t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact h3 m h
    · exact h3' m h
  zero_mem' := ⟨zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
  smul_mem' := by
    rintro x P ⟨h1, h2, h3⟩
    exact ⟨Submodule.smul_mem _ x h1, fun σ i i' h t => by rw [map_smul, h2 σ i i' h t],
      fun m hm => h3 m (support_smul hm)⟩

theorem det_gen_ne_zero (K : Type) [Field K] {Ix : Type} (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)).mapMatrix (gen K n t) = 1 := by
    ext p q
    simp [gen, Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem map_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {Ix : Type} (n : ℕ) (t : Ix) :
    (MvPolynomial.map f).mapMatrix (gen R n t) = gen S n t := by
  ext p q : 2
  simp [gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {n : ℕ}
  {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero K n t)

theorem map_cof {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Q : MvPolynomial (LtN Dw n) R) :
    MvPolynomial.map f (cof Dw pl R n Q) = cof Dw pl S n (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [algHom_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p ℓ hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cof, aeval_X]
    split_ifs with h1 h2 h3
    · simp [gen]
    · rw [← map_gen f, ← RingHom.map_adjugate]
      rfl
    · simp
    · simp

theorem isIntegral_coeff_cof {K : Type} [Field K] (P : MvPolynomial (LtN Dw n) K)
    (hP : ∀ m, P.coeff m ∈ (integralClosure ℤ K).toSubring) (m) : IsIntegral ℤ ((cof Dw pl K n P).coeff m) := by
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.map (integralClosure ℤ K).toSubring.subtype Q = P := by
    refine ⟨∑ m ∈ P.support, monomial m ⟨P.coeff m, hP m⟩, ?_⟩

    simp only [map_sum, map_monomial, Subring.subtype_apply]
    exact P.as_sum.symm
  rw [← map_cof, coeff_map]
  exact ((cof Dw pl _ n Q).coeff m).2



theorem exists_ioLFRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw := by
  intro E _ _ _ H Dw n Ix _ pl he hn l c a s lam ha hwt
  obtain ⟨ε, hε⟩ := GlobalTheory.T.frameReading_leadingMinorProduct_extremal E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨him, hex, heq⟩ := GlobalTheory.T.hodge_weight_dominance_condition E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨hpG, -, -⟩ := pG_mem_ne_zero_generates E H Dw n Ix pl he hn l c a ha
  obtain ⟨-, -, hstab⟩ := letAct_mul_one_mem_HHa E H Dw n Ix pl he hn c.F a
  obtain ⟨hs1, hs2, hs3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  have hD := detFac_ne_zero Dw pl c.F a s lam
  let S := harmSub Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
  have hS : ∀ P, P ∈ S ↔ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun _ => Iff.rfl
  set e : c.F := ((ε : ℤ) : c.F) with he'
  have hee : e * e = 1 := by
    rw [he', ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have heI : IsIntegral ℤ e := isIntegral_intCast _
  set D := detFac Dw pl c.F a s lam with hDdef
  have hex' : ∀ F : VVc c lam, ∃! P, P ∈ S ∧ cof Dw pl c.F n P = e • (D * F.1) := fun F => by
    have := hex (e • F.1) (Submodule.smul_mem _ _ F.2)
    rwa [mul_smul_comm] at this
  choose φ hφ huniq using hex'
  have hu : ∀ (F : VVc c lam) P, P ∈ S → cof Dw pl c.F n P = e • (D * F.1) → φ F = P :=
    fun F P h1 h2 => (huniq F P ⟨h1, h2⟩).symm
  let io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
    { toFun := φ
      map_add' := fun F G => hu _ _ (add_mem (hφ F).1 (hφ G).1) (by
        rw [map_add (f := _), (hφ F).2, (hφ G).2, Submodule.coe_add, mul_add, smul_add])
      map_smul' := fun x F => hu _ _ (Submodule.smul_mem _ _ (hφ F).1) (by
        rw [map_smul, (hφ F).2, Submodule.coe_smul, mul_smul_comm, smul_comm]; rfl) }
  have hio : ∀ F, io F = φ F := fun _ => rfl
  have hsurj : ∀ P ∈ S, ∃ F : VVc c lam, io F = P := fun P hP => by
    obtain ⟨F, hF, h⟩ := him P hP
    refine ⟨⟨e • F, Submodule.smul_mem _ _ hF⟩, hu _ _ hP ?_⟩
    rw [h, mul_smul_comm, smul_smul, hee, one_smul]
  have hwm : (ten fun t => extremal c.F n (lam t)) ∈ VV c.F lam := by
    obtain ⟨F, hF, h⟩ := him _ hpG.1
    rw [hε, ← mul_smul_comm] at h
    have h' := mul_left_cancel₀ hD h
    have : (ten fun t => extremal c.F n (lam t)) = e • F := by rw [← h', smul_smul, hee, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hF
  refine ⟨io, ⟨_, hwm⟩, rfl, fun ga => if h : IsUnit ga.det then
      ∏ t, (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) t : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F).det ^ (s t) else 0, hn, ?_, ?_, ?_, (hs1 _).2 hs2,
      fun x hx => hs3 x ((hs1 _).1 hx), hu _ _ hpG.1 hε, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro F hF
    have h := (hφ F).2
    rw [← hio, hF, map_zero] at h
    have h' := congrArg (fun x => e • x) h
    simp only [smul_zero, smul_smul, hee, one_smul] at h'
    exact Subtype.ext ((mul_eq_zero.1 h'.symm).resolve_left hD)
  · have : Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) = S :=
      Submodule.span_eq S
    rw [this]
    refine le_antisymm ?_ hsurj
    rintro _ ⟨F, rfl⟩
    exact (hφ F).1
  · intro ga hga F
    have h : IsUnit ga.det := by
      have := congrArg Matrix.det hga
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    rw [gaStar_conj_eq_letAct E H Dw n Ix pl he hn l c ga h hga]
    simp only [dif_pos h, rhoM]
    set g := invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) with hg
    refine hu _ _ (Submodule.smul_mem _ _ (hstab g _ (hφ F).1)) ?_
    have h1 := heq g _ (hφ F).1 (e • F.1) (Submodule.smul_mem _ _ F.2) (by rw [(hφ F).2, mul_smul_comm])
    rw [map_smul, hio, h1, smul_smul, ← Finset.prod_mul_distrib, map_smul, mul_smul_comm]
    have h2 : ∏ t, (g t : Matrix (Fin n) (Fin n) c.F).det ^ (s t) * (g t : Matrix (Fin n) (Fin n) c.F).det ^ (-(s t)) = 1 :=
      Finset.prod_eq_one fun t _ => by
        rw [← zpow_add₀ (Matrix.isUnits_det_units (g t)).ne_zero, add_neg_cancel, zpow_zero]
    rw [h2, one_smul]
    rfl
  · intro P hP
    obtain ⟨F, rfl⟩ := hsurj P hP.1
    refine ⟨F, (hs1 F).2 (GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral c.F Ix n lam
      (fun t => ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) F.1 F.2 fun m => ?_), rfl⟩
    have h : e • cof Dw pl c.F n (φ F) = D * F.1 := by rw [(hφ F).2, smul_smul, hee, one_smul]
    change IsIntegral ℤ ((D * F.1).coeff m)
    rw [← h, MvPolynomial.coeff_smul, smul_eq_mul]
    exact heI.mul (isIntegral_coeff_cof Dw pl (φ F) hP.2 m)

end GlobalTheory.FrameRead.CoefMap
end
end
end
