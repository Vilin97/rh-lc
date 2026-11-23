module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame

section

section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Ind

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

def Keeps (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Prop := ∀ t, q t = 0 → q (L t) = 0

def indOp (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Module.End ℂ P :=
  if h : Function.Surjective q ∧ Keeps q L then
    (q.quotKerEquivOfSurjective h.1).toLinearMap ∘ₗ
      ((LinearMap.ker q).mapQ (LinearMap.ker q) L fun t ht => LinearMap.mem_ker.2 (h.2 t (LinearMap.mem_ker.1 ht))) ∘ₗ
        (q.quotKerEquivOfSurjective h.1).symm.toLinearMap
  else 0

theorem indOp_apply {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L) (t : T) :
    indOp q L (q t) = q (L t) := by
  have e : (q.quotKerEquivOfSurjective hq).symm (q t) = Submodule.Quotient.mk t :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  rw [indOp, dite_eq_left ⟨hq, hL⟩, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem indOp_eq {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L)
    (M : Module.End ℂ P) (h : ∀ t, M (q t) = q (L t)) : indOp q L = M := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  rw [indOp_apply hq hL, h]

theorem keeps_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L * L') :=
  fun t ht => h _ (h' t ht)

theorem keeps_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L - L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem indOp_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L * L') = indOp q L * indOp q L' :=
  indOp_eq hq (keeps_mul h h') _ fun t => by
    rw [Module.End.mul_apply, indOp_apply hq h', indOp_apply hq h]; rfl

theorem indOp_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L - L') = indOp q L - indOp q L' :=
  indOp_eq hq (keeps_sub h h') _ fun t => by
    rw [LinearMap.sub_apply, indOp_apply hq h', indOp_apply hq h, LinearMap.sub_apply, map_sub]

end Ind

section Place

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp only [Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]

theorem atPl_comm {w w' : ι} (hw : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp only [Function.update_self, Function.update_of_ne hw]; first | rfl | simp [Module.End.mul_eq_comp]
  · by_cases h' : i = w'
    · subst h'; simp only [Function.update_self, Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]
    · simp only [Function.update_of_ne h, Function.update_of_ne h']

end Place

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

def fockOp (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if h : Function.Surjective q ∧ ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y)) then
    { toFun := fun Y => indOp q (atPl w (fockAct2 p₁ q₁ r s Y))
      map_add' := fun Y Z => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [LinearMap.add_apply, indOp_apply h.1 (h.2 Y), indOp_apply h.1 (h.2 Z), map_add (f := _), Main.atPl_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c Y => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [RingHom.id_apply, LinearMap.smul_apply, indOp_apply h.1 (h.2 Y), map_smul, Main.atPl_smul,
          LinearMap.smul_apply, map_smul] }
  else 0

theorem fockOp_eq {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) :
    fockOp q w Y = indOp q (atPl w (fockAct2 p₁ q₁ r s Y)) := by
  rw [fockOp, dite_eq_left ⟨hq, hK⟩]
  rfl

theorem fockOp_apply {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) (t : Tens F p₁ q₁ r s) :
    fockOp q w Y (q t) = q (atPl w (fockAct2 p₁ q₁ r s Y) t) := by
  rw [fockOp_eq hq hK, indOp_apply hq (hK Y)]


variable (r s) in
def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem negT_apply (Y : Mat r s) : negT r s Y = -Yᵀ := rfl

def twAct (ε : Bool) (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if ε then fockOp q w else fockOp q w ∘ₗ negT r s

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsFrames (B : Base F E) {n d : ℕ} (Y : Spc F E n) (W : Spc F E d) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) : Prop :=
  Framed B.emb (incM F Y.J) (incM F W.J) 1 Complex.I A C ∧ (∀ w, Y.θ w * A w = A w * Jm p₁ q₁) ∧
    ∀ w, W.θ w * C w = C w * Jm r s

def IsFockData (B : Base F E) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ)
    (Φ : Tens F p₁ q₁ r s →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  IsFrames B Y W A C ∧ IsFockMap B.ψ B.emb M.co A C Φ

def IsAdaptedFrame (B : Base F E) {d d₁ : ℕ} (H' : Plane E d d₁) {r s : ℕ}
    (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) (r₀ : Fin r) (s₀ : Fin s) : Prop :=
  ∀ w, (∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C w i (.inl r₀) + C w i (.inr s₀))) ∧
    (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C w i (.inl r₀) + c₂ * C w i (.inr s₀)) ∧
    ∀ a, a ≠ .inl r₀ → a ≠ .inr s₀ → ∃ z : Fin d₁ → ℂ, ∀ i, C w i a = (H'.ι.map (B.emb w).1 *ᵥ z) i

end Frames

section Laws

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

theorem atPl_sub {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' := by
  simp only [Main.atPl_eq, MultilinearMap.map_update_sub]

theorem fockOp_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y Z : Mat r s) :
    fockOp q w (Y * Z - Z * Y) = fockOp q w Y * fockOp q w Z - fockOp q w Z * fockOp q w Y := by
  rw [fockOp_eq hq hK, fockOp_eq hq hK, fockOp_eq hq hK, (GlobalTheory.FockPair.pair_lie_commute p₁ q₁ r s).2.1 Y Z,
    atPl_sub, atPl_mul, atPl_mul, indOp_sub hq (keeps_mul (hK Y) (hK Z)) (keeps_mul (hK Z) (hK Y)),
    indOp_mul hq (hK Y) (hK Z), indOp_mul hq (hK Z) (hK Y)]

theorem fockOp_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) {w w' : InfinitePlace F} (hw : w ≠ w') (Y Z : Mat r s) :
    fockOp q w Y * fockOp q w' Z = fockOp q w' Z * fockOp q w Y := by
  rw [fockOp_eq hq (hK w), fockOp_eq hq (hK w'), ← indOp_mul hq (hK w Y) (hK w' Z),
    ← indOp_mul hq (hK w' Z) (hK w Y), atPl_comm hw]

theorem negT_negT (Y : Mat r s) : negT r s (negT r s Y) = Y := by
  simp [negT_apply]

theorem negT_lie (Y Z : Mat r s) : negT r s (Y * Z - Z * Y) = negT r s Y * negT r s Z - negT r s Z * negT r s Y := by
  simp only [negT_apply, Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

theorem sameBlock_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem isKC_negT {Y : Mat r s} (hY : IsKC Y) : IsKC (negT r s Y) := fun a b hab => by
  rw [negT_apply, Matrix.neg_apply, Matrix.transpose_apply, hY b a fun h => hab (sameBlock_symm h), neg_zero]

theorem negT_Eab (a b : Ix r s) : negT r s (Eab a b) = -Eab b a := by
  rw [negT_apply, Eab, Eab, Matrix.transpose_single]

theorem twAct_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) (Y Z : Mat r s) :
    twAct ε q w (Y * Z - Z * Y) = twAct ε q w Y * twAct ε q w Z - twAct ε q w Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    rw [negT_lie, fockOp_lie hq hK]
  · simp only [twAct, if_true]
    exact fockOp_lie hq hK Y Z

theorem twAct_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) {w w' : InfinitePlace F} (hw : w ≠ w')
    (Y Z : Mat r s) : twAct ε q w Y * twAct ε q w' Z = twAct ε q w' Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    exact fockOp_comm hq hK hw _ _
  · simp only [twAct, if_true]
    exact fockOp_comm hq hK hw _ _

end Laws

end GlobalTheory.FockBridge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JmConjTranspose

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Alg

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

theorem isExp_mem {L U : Module.End ℂ V} (hU : IsExp L U) (N : Submodule ℂ V) (hN : ∀ v ∈ N, L v ∈ N) {T : V}
    (hT : T ∈ N) : U T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  have hp : ∀ n : ℕ, (L ^ n) T ∈ N := fun n => by
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have h := hU T (l' ∘ₗ N.mkQ)
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((L ^ n) T)) = fun _ => 0 := by
    funext n
    simp [(Submodule.Quotient.mk_eq_zero N).2 (hp n)]
  rw [e] at h
  exact h.unique hasSum_zero

theorem isExp_eig {L U : Module.End ℂ V} (hU : IsExp L U) (q : V →ₗ[ℂ] Z) (L0 : Module.End ℂ Z)
    (h : ∀ v, q (L v) = L0 (q v)) {T : V} {μ : ℂ} (hT : L0 (q T) = μ • q T) : q (U T) = Complex.exp μ • q T := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul]
  have hp : ∀ n : ℕ, q ((L ^ n) T) = μ ^ n • q T := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, hT, smul_smul, pow_succ]
  have a := hU T (l ∘ₗ q)
  simp only [LinearMap.comp_apply, hp, map_smul, smul_eq_mul] at a
  have b := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).mul_right (l (q T))
  rw [← Complex.exp_eq_exp_ℂ] at b
  simp only [smul_eq_mul, mul_assoc] at b
  exact a.unique b

theorem exp_mul_eq {a b : ℂ} (h : ∀ s : ℝ, Complex.exp (s * a) = Complex.exp (s * b)) : a = b := by
  have d : ∀ z : ℂ, HasDerivAt (fun s : ℝ => Complex.exp (s * z)) z 0 := fun z => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const z
    simpa using h1.cexp
  have e : (fun s : ℝ => Complex.exp (s * a)) = fun s : ℝ => Complex.exp (s * b) := funext h
  exact (d a).unique (e ▸ d b)

theorem bottom_of_sum (D₁ D₂ : Module.End ℂ V) (a : ℂ) {v : V}
    (hv : v ∈ ⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) (h0 : D₁ v + D₂ v = 0) :
    D₁ v = a • v ∧ D₂ v = (-a) • v := by
  have hle : (⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) ≤
      (D₁.eigenspace a ⊓ D₂.eigenspace (-a)) ⊔ ⨆ μ ≠ (0 : ℂ), (D₁ + D₂).eigenspace μ := by
    refine iSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · refine le_sup_of_le_right (le_iSup₂_of_le ((n.1 + n.2 : ℕ) : ℂ) ?_ ?_)
      · rw [Nat.cast_ne_zero]
        intro h; apply hn; ext <;> simp <;> omega
      · intro x hx
        have h1 := Module.End.mem_eigenspace_iff.1 hx.1
        have h2 := Module.End.mem_eigenspace_iff.1 hx.2
        rw [Module.End.mem_eigenspace_iff, LinearMap.add_apply, h1, h2, ← add_smul]
        congr 1; push_cast; ring
  obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hle hv)
  have h1 := Module.End.mem_eigenspace_iff.1 hy.1
  have h2 := Module.End.mem_eigenspace_iff.1 hy.2
  have hz0 : z ∈ (D₁ + D₂).eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, show z = v - y by rw [← e]; abel, map_sub, LinearMap.add_apply, h0,
      LinearMap.add_apply, h1, h2]
    simp
  have := (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep (D₁ + D₂)) 0)) z hz0 hz
  rw [this, add_zero] at e
  exact e ▸ ⟨h1, h2⟩

theorem eq_zero_of_below (D : Module.End ℂ V) (a : ℂ) {ι : Type} (f : ι → ℕ) (N : ι → Submodule ℂ V)
    (hN : ∀ i, N i ≤ D.eigenspace (a + f i)) {v : V} (hv : v ∈ ⨆ i, N i) (h : D v = (a - 1) • v) : v = 0 := by
  have hle : (⨆ i, N i) ≤ ⨆ μ ≠ (a - 1), D.eigenspace μ := by
    refine iSup_le fun i => le_iSup₂_of_le (a + f i) ?_ (hN i)
    intro e
    have : ((f i + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination e
    exact Nat.succ_ne_zero _ (Nat.cast_eq_zero.1 this)
  exact (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep D) (a - 1))) v
    (Module.End.mem_eigenspace_iff.2 h) (hle hv)

end Alg

section Mat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_col {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (a : n) :
    NormedSpace.exp Y a c = if a = c then Complex.exp μ else 0 := by
  have hp : ∀ (k : ℕ) a, (Y ^ k) a c = if a = c then μ ^ k else 0 := fun k => by
    induction k with
    | zero => intro a; simp [Matrix.one_apply]
    | succ k ih =>
      intro a
      rw [pow_succ', Matrix.mul_apply]
      simp only [ih, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h]
      split_ifs <;> simp [pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mapL
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c))
  have e : ∀ M : Matrix n n ℂ, LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c) M = M a c := fun _ => rfl
  simp only [e, Matrix.smul_apply, hp] at h1
  split_ifs at h1 ⊢
  · rw [Complex.exp_eq_exp_ℂ]
    exact h1.unique (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ)
  · simp only [smul_zero] at h1
    exact h1.unique hasSum_zero

theorem mul_exp_col {m n : Type} [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (i : m) :
    (C * NormedSpace.exp Y) i c = Complex.exp μ * C i c := by
  rw [Matrix.mul_apply]
  simp [exp_col Y c μ h, mul_comm]

end Mat

theorem jm_conjTranspose (R S : ℕ) : (Formalism.BasicNotions.TH.Jm R S)ᴴ = Formalism.BasicNotions.TH.Jm R S := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ Y₁ ∈ upq R S, ∃ Y₂ ∈ upq R S, Z = Y₁ + Complex.I • Y₂ := by
  set J := Formalism.BasicNotions.TH.Jm R S
  have hJ : J * J = 1 := GlobalTheory.FockKStab.jm_mul_jm R S
  have hJ' : Jᴴ = J := jm_conjTranspose R S
  have h1 : ∀ M : Mat R S, J * (J * M) = M := fun M => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z - J * Zᴴ * J), ?_, (1 / (2 * Complex.I)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / 2 : ℂ) = 1 / 2 by simp, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    simp
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul,
      Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    rw [add_comm]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - J * Zᴴ * J + (Z + J * Zᴴ * J) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d}

def genOp (P Q : ℕ) (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) : Module.End ℂ (Tens F P Q R S) :=
  sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) fun w => fockAct2 P Q R S (Yg w) + (c w * (Yg w).trace) • 1

theorem genOp_apply (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (T : Tens F P Q R S) :
    genOp P Q c Yg T = ∑ w, (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S (Yg w)) T +
      (c w * (Yg w).trace) • T) := by
  simp [genOp, sumPl, LinearMap.sum_apply, Main.atPl_add, Main.atPl_smul, Main.atPl_one]

theorem genOp_single (c : InfinitePlace F → ℂ) (w : InfinitePlace F) (Z : Mat R S) (T : Tens F P Q R S) :
    genOp P Q c (Pi.single w Z) T = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T +
      (c w * Z.trace) • T := by
  rw [genOp_apply, Finset.sum_eq_single w]
  · simp
  · intro w' _ h
    simp [Pi.single_eq_of_ne h, Main.atPl_zero]
  · simp

theorem genOp_smul (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (s : ℂ) :
    genOp P Q c (s • Yg) = s • genOp P Q c Yg := by
  refine LinearMap.ext fun T => ?_
  rw [LinearMap.smul_apply, genOp_apply, genOp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, map_smul, Main.atPl_smul, LinearMap.smul_apply, Matrix.trace_smul, smul_add, smul_smul,
    smul_eq_mul]
  congr 2; ring

theorem genOp_locFin (c : InfinitePlace F → ℂ) {Yg : InfinitePlace F → Mat R S} (h : ∀ w, IsKC (Yg w)) :
    LocFin (genOp P Q c Yg) :=
  Main.i_locfin _ _ _ fun w => Main.locFin_fock2 P Q R S (Yg w) (h w) _

variable {B : Base F E} {om : Rep σ Y W} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
  {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {c : InfinitePlace F → ℂ}

theorem acts_unique {T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ f₂ : SInf F (Fin n × Fin d)}
    (h₁ : Acts (evI F) T f f₁) (h₂ : Acts (evI F) T f f₂) : f₁ = f₂ :=
  (Main.i_actslaws F _ f f₁ f₂).2.2.2.1 T h₁ h₂

theorem exp_of_gen (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {γ : Multiplicative ℝ →* UG (cA σ) (incM F W.J)} (hγ : γ ∈ RLines (σ := σ) (incM F W.J)) {Yg : InfinitePlace F → Mat R S}
    (hY : IsGen B.emb C γ Yg) (hKC : ∀ w, IsKC (Yg w)) :
    ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧
      ∀ T, Acts (evI F) (om (1, γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) := by
  obtain ⟨U, hU, hSA⟩ := Main.i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
    (genOp_locFin c hKC) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hY T)
  exact ⟨U, hU, fun T => (Main.i_actslaws F _ (Φ T) (Φ (U T)) (Φ T)).2.1 _ (map_zero _) (hSA T)⟩

theorem exp_of_kInf (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ (Yg : InfinitePlace F → Mat R S) (U : Module.End ℂ (Tens F P Q R S)), (∀ w, IsKC (Yg w)) ∧
      IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    Main.i_kline Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C W.θ hcm hC hθ k hk.1 hk.2
  obtain ⟨U, hU, hA⟩ := exp_of_gen hact hadm hγ hgen hKC
  exact ⟨Yg, U, hKC, hU, hγ1 ▸ hA⟩

theorem exp_of_skew (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (Yg : InfinitePlace F → Mat R S) (hKC : ∀ w, IsKC (Yg w)) (hs : ∀ w, (Yg w)ᴴ = -Yg w) :
    ∃ k ∈ KInf σ W B.emb, (∀ w, (mat k).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w)) ∧
      ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC Yg
    fun w => GlobalTheory.FockKStab.mem_upq (hKC w) (hs w)
  have h1 : ∀ w, (mat (γ (Multiplicative.ofAdd 1))).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w) := fun w => by
    have := hgen 1 w
    rwa [one_smul] at this
  refine ⟨γ (Multiplicative.ofAdd 1), ⟨hγ.2 _, fun w => ?_⟩, h1, exp_of_gen hact hadm hγ hgen hKC⟩
  obtain ⟨A', hA'⟩ := (hC w).2
  exact GlobalTheory.FockKStab.commute_of_frame hA' (GlobalTheory.FockKStab.frame_inv (hC w) hA') (h1 w) (hθ w)
    (Commute.exp_left (GlobalTheory.FockKStab.commute_jm (hKC w)))

theorem eq_of_frame (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    {k k' : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) (hk' : k' ∈ UAt σ W (evI F))
    (h : ∀ w, (mat k).map (piInf (B.emb w)) * C w = (mat k').map (piInf (B.emb w)) * C w) : k = k' := by
  apply Subtype.ext; apply Units.ext
  show mat k = mat k'
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm B.emb _ (fun u hu => ?_) fun w => ?_
  · have a := congrFun (congrFun (hk u hu) i) j
    have b := congrFun (congrFun (hk' u hu) i) j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] at a b
    rw [show mat k i j - mat k' i j = (mat k i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) -
      (mat k' i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) by ring, smul_sub, a, b, sub_zero]
  · obtain ⟨A', hA'⟩ := (hC w).2
    have e := congrArg (· * A') (h w)
    simp only [Matrix.mul_assoc, hA', Matrix.mul_one] at e
    have := congrFun (congrFun e i) j
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]

theorem stab_of_fix (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (I : Set (Ix R S)) (N : Submodule ℂ (Tens F P Q R S))
    (hN : ∀ k ∈ KInf σ W B.emb, (∀ w, ∀ b ∈ I, ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i b = C w i b) →
      ∀ T ∈ N, ∀ T', Acts (evI F) (om (1, k)) (Φ T) (Φ T') → T' ∈ N)
    (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z) (hI : ∀ b ∈ I, ∀ a, Z a b = 0 ∧ Z b a = 0) {T : Tens F P Q R S}
    (hT : T ∈ N) : atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T ∈ N := by
  have key : ∀ Y : Mat R S, IsKC Y → Yᴴ = -Y → (∀ b ∈ I, ∀ a, Y a b = 0) →
      atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T ∈ N := by
    intro Y hY hs h0
    have hKC : ∀ (s : ℂ) w', IsKC ((s • (Pi.single w Y : InfinitePlace F → Mat R S)) w') := fun s w' => by
      refine GlobalTheory.FockKStab.isKC_smul ?_ s
      by_cases h : w' = w
      · subst h; simpa using hY
      · simpa [Pi.single_eq_of_ne h] using GlobalTheory.FockKStab.isKC_zero R S
    have hmem := GlobalTheory.FockKStab.mem_of_exp (genOp P Q c (Pi.single w Y)) (genOp_locFin c (by simpa using hKC 1)) N T
      fun s => by
        obtain ⟨k, hk, hkC, U, hU, hA⟩ := exp_of_skew hcm hC hθ hact hadm ((s : ℂ) • Pi.single w Y) (hKC s) fun w' => by
          by_cases h : w' = w
          · subst h; simp [Matrix.conjTranspose_smul, hs]
          · simp [Pi.single_eq_of_ne h]
        refine ⟨U, genOp_smul c _ (s : ℂ) ▸ hU, hN k hk (fun w' b hb i => ?_) T hT _ (hA T)⟩
        rw [hkC, mul_exp_col _ _ b 0, Complex.exp_zero, one_mul]
        intro a
        by_cases h : w' = w
        · subst h; simp [h0 b hb a]
        · simp [Pi.single_eq_of_ne h]
    rw [genOp_single] at hmem
    simpa using N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)
  have hZh : IsKC Zᴴ := GlobalTheory.FockKStab.isKC_conjTranspose hZ
  have hZ' : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + Complex.I • (1 / (2 * Complex.I)) • (Z + Zᴴ) := by
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  rw [hZ', map_add (f := _), map_smul _ Complex.I, Main.atPl_add, Main.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
  refine N.add_mem (key _ ?_ ?_ ?_) (N.smul_mem _ (key _ ?_ ?_ ?_))
  · exact GlobalTheory.FockKStab.isKC_smul (fun a b h => by rw [Matrix.sub_apply, hZ a b h, hZh a b h, sub_zero]) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]
  · exact GlobalTheory.FockKStab.isKC_smul (GlobalTheory.FockKStab.isKC_add hZ hZh) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]

end Tens

end GlobalTheory.FockBottom
end
end
end
