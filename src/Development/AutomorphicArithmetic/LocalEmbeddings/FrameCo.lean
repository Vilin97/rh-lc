module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TangentOrigin
open GlobalTheory.Twist (resM resM_resM resM_smul)

namespace GlobalTheory.BcLie

variable {X X' : Scheme.{0}} {M : X.Modules} {r : ℕ} {K K' : Type} [CommRing K] [CommRing K']

def trS (c c' : Chart M r) : Matrix (Fin r) (Fin r) Γ(X, c.U ⊓ c'.U) :=
  Matrix.of fun a b => (c.isFrame.basis inf_le_left).repr (resM M inf_le_right (c'.e b)) a


open Classical in
def trAt (x : Sp K ⟶ X) (c c' : Chart M r) : Matrix (Fin r) (Fin r) K :=
  if h : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) then (trS c c').map (evalPt x _ h) else 0

def IsCo (ξ : Sp K ⟶ X) (A : Chart M r → Matrix (Fin r) (Fin r) K) : Prop :=
  (∀ c : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → IsUnit (A c).det) ∧
    ∀ c c' : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → ⊤ ≤ ξ ⁻¹ᵁ c'.U → A c' = A c * trAt ξ c c'

def IsAdapted (fl : Vert.Flag M r) (c : Chart M r) : Prop :=
  ∀ i : Fin r, ∃ s : Γ(fl.F i.succ, c.U), (fl.ι i.succ).app c.U s = c.e i

def IsTri (T : Matrix (Fin r) (Fin r) K) : Prop := ∀ a i, i < a → T a i = 0

def pos (dual : Bool) (i : Fin r) : Fin r := cond dual i.rev i

def lieMat (dual : Bool) (A : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K := cond dual (A⁻¹)ᵀ A

theorem le_inf_pre {x : Sp K ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun p hp => ⟨h hp, h' hp⟩

theorem trAt_eq {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    trAt x c c' = (trS c c').map (evalPt x _ h) := dif_pos h

theorem trAt_apply {x : Sp K ⟶ X} (c c' : Chart M r) {W : X.Opens} (h₁ : W ≤ c.U) (h₂ : W ≤ c'.U) (h : ⊤ ≤ x ⁻¹ᵁ W)
    (a b : Fin r) : trAt x c c' a b = evalPt x W h ((c.isFrame.basis h₁).repr (resM M h₂ (c'.e b)) a) := by
  have hW : W ≤ c.U ⊓ c'.U := le_inf h₁ h₂
  have h' : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) := fun p hp => hW (h hp)
  rw [trAt_eq c c' h', map_apply, trS, of_apply, ← evalPt_res x hW h' h, ← c.isFrame.repr_resM, resM_resM]

theorem trAt_self {x : Sp K ⟶ X} (c : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) : trAt x c c = 1 := by
  apply Matrix.ext
  intro a b
  rw [trAt_apply c c le_rfl le_rfl h, ← c.isFrame.basis_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  simp only [eq_comm (a := a)]
  split_ifs <;> simp

theorem trAt_mul {x : Sp K ⟶ X} (c c' c'' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (h'' : ⊤ ≤ x ⁻¹ᵁ c''.U) : trAt x c c' * trAt x c' c'' = trAt x c c'' := by
  have hW := le_inf_pre (le_inf_pre h h') h''
  have l₁ : c.U ⊓ c'.U ⊓ c''.U ≤ c.U := inf_le_left.trans inf_le_left
  have l₂ : c.U ⊓ c'.U ⊓ c''.U ≤ c'.U := inf_le_left.trans inf_le_right
  have l₃ : c.U ⊓ c'.U ⊓ c''.U ≤ c''.U := inf_le_right
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply, trAt_apply c c'' l₁ l₃ hW, ← (c'.isFrame.basis l₂).sum_repr (resM M l₃ (c''.e b))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, map_mul,
    IsFrame.basis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [trAt_apply c c' l₁ l₂ hW, trAt_apply c' c'' l₂ l₃ hW, mul_comm]

theorem isUnit_det_trAt {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
    IsUnit (trAt x c c').det :=
  isUnit_det_of_right_inverse ((trAt_mul c c' c h h' h).trans (trAt_self c h))

theorem trAt_spMap (φ : K →+* K') {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
    trAt (spMap φ ≫ x) c c' = (trAt x c c').map φ := by
  have hW := le_inf_pre h h'
  have hW' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ (c.U ⊓ c'.U) := fun p _ => hW (x := spMap φ p) trivial
  rw [trAt_eq c c' hW, trAt_eq c c' hW']
  ext a b
  exact evalPt_spMap_comp φ x _ hW hW' _

theorem lieMat_mul (dual : Bool) (A B : Matrix (Fin r) (Fin r) K) : lieMat dual (A * B) = lieMat dual A * lieMat dual B := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true, Matrix.mul_inv_rev, transpose_mul]

theorem isUnit_det_lieMat (dual : Bool) {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) : IsUnit (lieMat dual A).det := by
  cases dual
  · exact h
  · simp only [lieMat, cond_true, det_transpose]
    exact isUnit_nonsing_inv_det A h

theorem lieMat_lieMat (dual : Bool) {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) : lieMat dual (lieMat dual A) = A := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true]
    rw [← transpose_nonsing_inv, transpose_transpose, nonsing_inv_nonsing_inv _ h]

theorem lieMat_map (dual : Bool) (φ : K →+* K') {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) :
    lieMat dual (A.map φ) = (lieMat dual A).map φ := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true]
    rw [transpose_map]
    congr 1
    refine inv_eq_left_inv ?_
    rw [← Matrix.map_mul, nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem pos_pos (dual : Bool) (i : Fin r) : pos dual (pos dual i) = i := by
  cases dual <;> simp [pos]

end GlobalTheory.BcLie

end
