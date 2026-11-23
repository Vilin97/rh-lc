module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferPrism

section

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

theorem dc_cons {m : ℕ} (G : (Fin (m + 2) → Y) → ℝ) (a : Y) (t : Fin (m + 2) → Y) :
    dc G (Fin.cons a t) = G t - dc (fun z => G (Fin.cons a z)) t := by
  unfold dc
  rw [Fin.sum_univ_succ]
  have h0 : (fun j => (Fin.cons a t : Fin (m + 3) → Y) ((0 : Fin (m + 3)).succAbove j)) = t := by
    funext j; simp
  have hs : ∀ i : Fin (m + 2), (fun j => (Fin.cons a t : Fin (m + 3) → Y) (i.succ.succAbove j)) =
      Fin.cons a (fun j => t (i.succAbove j)) := by
    intro i; funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_succAbove_succ]
  rw [h0]
  simp only [hs, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_sub {m : ℕ} (G H : (Fin (m + 1) → Y) → ℝ) (x : Fin (m + 2) → Y) :
    dc (fun z => G z - H z) x = dc G x - dc H x := by
  unfold dc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc1 (G : (Fin 1 → Y) → ℝ) (y : Fin 2 → Y) :
    dc G y = G (fun _ => y 1) - G (fun _ => y 0) := by
  unfold dc
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h0 : (fun j : Fin 1 => y ((0 : Fin 2).succAbove j)) = fun _ => y 1 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  have h1 : (fun j : Fin 1 => y ((Fin.succ 0 : Fin 2).succAbove j)) = fun _ => y 0 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  rw [h0, h1]; simp; ring

def prism (φ : Y → Y) : (m : ℕ) → ((Fin (m + 2) → Y) → ℝ) → (Fin (m + 1) → Y) → ℝ
  | 0, F, x => F (Fin.cons (x 0) (φ ∘ x))
  | m + 1, F, x => F (Fin.cons (x 0) (φ ∘ x)) - prism φ m (fun z => F (Fin.cons (x 0) z)) (Fin.tail x)

theorem prism_sub (φ : Y → Y) : ∀ (m : ℕ) (F G : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 1) → Y),
    prism φ m (fun z => F z - G z) x = prism φ m F x - prism φ m G x
  | 0, F, G, x => rfl
  | m + 1, F, G, x => by
    simp only [prism]
    rw [prism_sub φ m]
    ring

theorem prism_zero (φ : Y → Y) : ∀ (m : ℕ) (x : Fin (m + 1) → Y),
    prism φ m (fun _ => (0 : ℝ)) x = 0
  | 0, x => rfl
  | m + 1, x => by
    simp only [prism]
    rw [prism_zero φ m]
    ring

theorem prism_base (φ : Y → Y) (F : (Fin 2 → Y) → ℝ) (x : Fin 2 → Y) :
    dc (prism φ 0 F) x + prism φ 1 (dc F) x = F (φ ∘ x) - F x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = Fin.cons a (fun _ : Fin 1 => b) := ⟨x 0, x 1, by
    funext j; refine Fin.cases rfl (fun k => ?_) j; rw [Fin.fin_one_eq_zero k]; rfl⟩
  simp only [prism, Fin.cons_zero, Fin.tail_cons]
  simp only [Fin.comp_cons]
  simp only [dc_cons, dc1]
  simp only [Fin.cons_zero, Fin.cons_one, Function.comp_def]
  ring

theorem prism_htpy (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 2) → Y),
    dc (prism φ m F) x + prism φ (m + 1) (dc F) x = F (φ ∘ x) - F x := by
  intro m
  induction m with
  | zero => exact prism_base φ
  | succ m ih =>
    intro F x
    obtain ⟨a, t, rfl⟩ : ∃ a t, x = Fin.cons a t := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [dc_cons]
    have hK : (fun z => prism φ (m + 1) F (Fin.cons a z)) =
        fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z))) - prism φ m (fun w => F (Fin.cons a w)) z := by
      funext z; simp only [prism, Fin.cons_zero, Fin.tail_cons, Fin.comp_cons]
    rw [hK, dc_sub]
    have h2 : prism φ (m + 2) (dc F) (Fin.cons a t) =
        dc F (Fin.cons a (φ ∘ Fin.cons a t)) - prism φ (m + 1) (fun z => dc F (Fin.cons a z)) t := by
      simp only [prism, Fin.cons_zero, Fin.tail_cons]
    rw [h2]
    have h3 : (fun z => dc F (Fin.cons a z)) = fun z => F z - dc (fun w => F (Fin.cons a w)) z := by
      funext z; exact dc_cons F a z
    rw [h3, prism_sub, Fin.comp_cons, dc_cons, dc_cons]
    have h4 : dc (fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z)))) t =
        dc (fun w => F (Fin.cons a (Fin.cons (φ a) w))) (φ ∘ t) := rfl
    rw [h4]
    linarith [ih (fun z => F (Fin.cons a z)) t]

theorem prism_smul {P : Type} [Group P] (φ : P → P) (k : P) (hφ : ∀ y, φ (k * y) = k * φ y) :
    ∀ (m : ℕ) (F : (Fin (m + 2) → P) → ℝ) (x : Fin (m + 1) → P),
      prism φ m F (fun i => k * x i) = prism φ m (fun z => F (fun i => k * z i)) x
  | 0, F, x => by
    simp only [prism]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hφ]
  | m + 1, F, x => by
    simp only [prism]
    have e1 : (Fin.cons (k * x 0) (φ ∘ fun i => k * x i) : Fin (m + 3) → P) =
        fun i => k * (Fin.cons (x 0) (φ ∘ x) : Fin (m + 3) → P) i := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hφ]
    rw [e1]
    congr 1
    have e2 : (Fin.tail fun i => k * x i) = fun i => k * Fin.tail x i := rfl
    rw [e2, prism_smul φ k hφ m]
    congr 1
    funext z
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferAlt

section

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral Polynomial

theorem pow_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v)) :
    ∀ (n : ℕ) (v : V), (T' ^ n) (L v) = L ((T ^ n) v)
  | 0, v => rfl
  | n + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, pow_intertwine T T' L h n]

theorem aeval_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v))
    (f : ℝ[X]) (v : V) : aeval T' f (L v) = L (aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_intertwine T T' L h n, map_smul]

theorem pow_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) : ∀ (n : ℕ) (v : V), v ∈ S → (T ^ n) v ∈ S
  | 0, v, hv => hv
  | n + 1, v, hv => by
    rw [pow_succ, Module.End.mul_apply]
    exact pow_mem T S hT n _ (hT v hv)

theorem aeval_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) (f : ℝ[X]) (v : V) (hv : v ∈ S) : aeval T f v ∈ S := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (pow_mem T S hT n v hv)

def invSub {P : Type} [Group P] (S : Set P) (m : ℕ) : Submodule ℝ ((Fin m → P) → ℝ) where
  carrier := {F | InvS S F}
  add_mem' {F G} hF hG g hg y := by simp only [Pi.add_apply, hF g hg y, hG g hg y]
  zero_mem' g _ y := rfl
  smul_mem' r F hF g hg y := by simp only [Pi.smul_apply, hF g hg y]

def dcL (Y : Type) (m : ℕ) : ((Fin (m + 1) → Y) → ℝ) →ₗ[ℝ] ((Fin (m + 2) → Y) → ℝ) where
  toFun := dc
  map_add' F G := by
    funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r F := by
    funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

def pullL {X Y : Type} (g : X → Y) (m : ℕ) : ((Fin m → Y) → ℝ) →ₗ[ℝ] ((Fin m → X) → ℝ) where
  toFun F x := F fun i => g (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismTransfer Polynomial

theorem transfer : Transfer := by
  intro P Q A _ _ _ pr s hs u hu ι hι hran φ hφ m hA q hq
  obtain ⟨f, hf1, hfA⟩ := hA q hq
  refine ⟨f, hf1, fun c hc hcc => ?_⟩
  set t := s u with ht
  have hker : ∀ k : P, k ∈ (pr.ker : Set P) ↔ pr k = 1 := fun k => MonoidHom.mem_ker

  let ρ : P → P := fun y => y * (s (pr y))⁻¹
  have hρk : ∀ y, ∃ a, ι a = ρ y := fun y => (hran _).1 (by simp [ρ, hs])
  let ρA : P → A := fun y => Classical.choose (hρk y)
  have hρA : ∀ y, ι (ρA y) = ρ y := fun y => Classical.choose_spec (hρk y)
  have hιk : ∀ b, pr (ι b) = 1 := fun b => (hran _).2 ⟨b, rfl⟩
  have hρmul : ∀ k y, pr k = 1 → ρ (k * y) = k * ρ y := by
    intro k y hk; simp only [ρ, map_mul, hk, one_mul, mul_assoc]
  have hρAmul : ∀ b y, ρA (ι b * y) = b * ρA y := by
    intro b y; apply hι; rw [map_mul, hρA, hρA, hρmul _ _ (hιk b)]
  have hcomm : ∀ g : Q, s g * t = t * s g := by
    intro g; rw [ht, ← map_mul, ← map_mul, hu]
  have hρconj : ∀ y, ρ (t⁻¹ * y * t) = t⁻¹ * ρ y * t := by
    intro y
    have hp : pr (t⁻¹ * y * t) = pr y := by
      rw [map_mul, map_mul, map_inv, ht, hs, hu, mul_inv_cancel_left]
    have hc' : (s (pr y))⁻¹ * t = t * (s (pr y))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show t⁻¹ * y * t * (s (pr (t⁻¹ * y * t)))⁻¹ = t⁻¹ * (y * (s (pr y))⁻¹) * t
    rw [hp]
    simp only [mul_assoc, hc']
  have hρAconj : ∀ y, ρA (t⁻¹ * y * t) = φ (ρA y) := by
    intro y; apply hι; rw [hρA, hρconj, hφ, hρA]

  let cA : (Fin (q + 2) → A) → ℝ := fun x => c fun i => ι (x i)
  have hcA : InvS Set.univ cA := by
    intro b _ x
    simp only [cA, map_mul]
    exact hc (ι b) ((hker _).2 (hιk b)) _
  have hccA : dc cA = 0 := by
    funext x
    have := congrFun hcc (fun i => ι (x i))
    simpa [dc, cA] using this
  obtain ⟨eA, heA, hfe⟩ := hfA cA hcA hccA

  let T : (n : ℕ) → Module.End ℝ ((Fin n → P) → ℝ) := fun n => mapOp (fun y => t⁻¹ * y * t) n
  have hTR : ∀ (n : ℕ) (g : (Fin n → A) → ℝ),
      T n (pullL ρA n g) = pullL ρA n (mapOp φ n g) := by
    intro n g; funext y; simp only [T, mapOp, pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAconj]
  have hTd : ∀ (n : ℕ) (F : (Fin (n + 1) → P) → ℝ), T (n + 2) (dcL P n F) = dcL P n (T (n + 1) F) :=
    fun n F => rfl
  have hRd : ∀ (n : ℕ) (g : (Fin (n + 1) → A) → ℝ), pullL ρA (n + 2) (dcL A n g) = dcL P n (pullL ρA (n + 1) g) :=
    fun n g => rfl

  have hpr : c = pullL ρA (q + 2) cA - dc (prism ρ q c) := by
    funext y
    have h1 := prism_htpy ρ q c y
    rw [hcc] at h1
    have h0 : prism ρ (q + 1) (fun _ => (0 : ℝ)) y = 0 := prism_zero ρ (q + 1) y
    have h2 : pullL ρA (q + 2) cA y = c (ρ ∘ y) := by
      simp only [pullL, cA, LinearMap.coe_mk, AddHom.coe_mk, hρA]; rfl
    simp only [Pi.sub_apply, h2]
    have h3 : (0 : (Fin (q + 3) → P) → ℝ) = fun _ => 0 := rfl
    rw [h3, h0] at h1
    linarith

  have hprismInv : InvS (pr.ker : Set P) (prism ρ q c) := by
    intro k hk y
    rw [prism_smul ρ k (fun y => hρmul k y ((hker k).1 hk)) q c y]
    congr 1
    funext z
    exact hc k hk z
  have hTinv : ∀ (n : ℕ), ∀ F ∈ invSub (pr.ker : Set P) n, T n F ∈ invSub (pr.ker : Set P) n := by
    intro n F hF k hk y
    simp only [T, mapOp, LinearMap.coe_mk, AddHom.coe_mk]
    have hk' : t⁻¹ * k * t ∈ (pr.ker : Set P) := by
      rw [hker] at hk ⊢
      rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
    have := hF _ hk' (fun i => t⁻¹ * y i * t)
    simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
    exact this
  refine ⟨pullL ρA (q + 1) eA - aeval (T (q + 1)) f (prism ρ q c), ?_, ?_⟩
  · intro k hk y
    obtain ⟨b, rfl⟩ := (hran k).1 ((hker k).1 hk)
    have h1 : aeval (T (q + 1)) f (prism ρ q c) ∈ invSub (pr.ker : Set P) (q + 1) :=
      aeval_mem _ _ (hTinv (q + 1)) f _ hprismInv
    simp only [Pi.sub_apply]
    rw [h1 (ι b) hk y]
    congr 1
    simp only [pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAmul]
    exact heA b trivial _
  · have e1 : aeval (T (q + 2)) f c =
        aeval (T (q + 2)) f (pullL ρA (q + 2) cA) - aeval (T (q + 2)) f (dcL P q (prism ρ q c)) := by
      conv_lhs => rw [hpr]
      rw [map_sub]
      rfl
    change aeval (T (q + 2)) f c = _
    rw [e1, aeval_intertwine (mapOp φ (q + 2)) (T (q + 2)) (pullL ρA (q + 2)) (hTR (q + 2)),
      aeval_intertwine (T (q + 1)) (T (q + 2)) (dcL P q) (hTd q), hfe]
    rw [show dc eA = dcL A q eA from rfl, hRd]
    rw [← map_sub]
    rfl

end PositivityTheory.KB.SplitAffineSpectral

end
end
end
