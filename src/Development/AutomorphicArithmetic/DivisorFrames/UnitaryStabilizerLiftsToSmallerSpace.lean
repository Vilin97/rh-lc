module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (c : R →+* R)

private def sqf {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : Fin n → R) : R := a ⬝ᵥ J *ᵥ fun i => c (b i)

private theorem sqf_mul {n m : ℕ} (J : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) (a b : Fin m → R) :
    sqf c J (A *ᵥ a) (A *ᵥ b) = sqf c (Aᵀ * J * A.map c) a b := by
  have h : (fun i => c ((A *ᵥ b) i)) = A.map c *ᵥ fun i => c (b i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [sqf, sqf, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec a, Matrix.vecMul_transpose]

private theorem sqf_ext {n : ℕ} (J J' : Matrix (Fin n) (Fin n) R) (h : ∀ a b, sqf c J a b = sqf c J' a b) : J = J' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have e : (fun k => c ((Pi.single j 1 : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j <;> simp [hk]
  simpa [sqf, e] using h1

private theorem sqf_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a a' b : Fin n → R) :
    sqf c J (a + a') b = sqf c J a b + sqf c J a' b := add_dotProduct _ _ _

private theorem sqf_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (r : R) (a b : Fin n → R) :
    sqf c J (r • a) b = r * sqf c J a b := smul_dotProduct _ _ _

private theorem sqf_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b b' : Fin n → R) :
    sqf c J a (b + b') = sqf c J a b + sqf c J a b' := by
  have e : (fun i => c ((b + b') i)) = (fun i => c (b i)) + fun i => c (b' i) := funext fun i => map_add _ _ _
  rw [sqf, e, Matrix.mulVec_add, dotProduct_add]; rfl

private theorem sqf_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (r : R) (a b : Fin n → R) :
    sqf c J a (r • b) = c r * sqf c J a b := by
  have e : (fun i => c ((r • b) i)) = c r • fun i => c (b i) := funext fun i => map_mul _ _ _
  rw [sqf, e, Matrix.mulVec_smul, dotProduct_smul]; rfl

private theorem sqf_symm (hc : ∀ z, c (c z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = J i j)
    (a b : Fin n → R) : sqf c J b a = c (sqf c J a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sqf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mat_ext {n : ℕ} {A A' : Matrix (Fin n) (Fin n) R} (h : ∀ z, A *ᵥ z = A' *ᵥ z) : A = A' := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

private theorem core (hc : ∀ z, c (c z) = z) {n m : ℕ} (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = J i j)
    (J₁ : Matrix (Fin m) (Fin m) R) (x y : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (π : Matrix (Fin m) (Fin n) R)
    (q1 : π * ι = 1)
    (q2 : ι * π + Matrix.vecMulVec x (J *ᵥ fun i => c (y i)) + Matrix.vecMulVec y (J *ᵥ fun i => c (x i)) = 1)
    (ox : ∀ u, sqf c J (ι *ᵥ u) x = 0) (oy : ∀ u, sqf c J (ι *ᵥ u) y = 0)
    (xx : sqf c J x x = 0) (yy : sqf c J y y = 0) (xy : sqf c J x y = 1) (gram : ιᵀ * J * ι.map c = J₁)
    (K K' : Matrix (Fin n) (Fin n) R) (hK : K * K' = 1) (hK' : K' * K = 1) (hu : Kᵀ * J * K.map c = J)
    (hu' : K'ᵀ * J * K'.map c = J) (t : Rˣ) (hx : K *ᵥ x = t.1 • x) :
    ∃ (G' : Matrix (Fin m) (Fin m) R) (M M' : Matrix (Fin n) (Fin n) R),
      π * K * ι * G' = 1 ∧ G' * (π * K * ι) = 1 ∧ (π * K * ι)ᵀ * J₁ * (π * K * ι).map c = J₁ ∧
      M * M' = 1 ∧ M' * M = 1 ∧ Mᵀ * J * M.map c = J ∧ M *ᵥ x = t.1 • x ∧ M *ᵥ y = c (t⁻¹).1 • y ∧
      M * ι = ι * (π * K * ι) ∧ (K * M') *ᵥ x = x ∧ ∀ z, ∃ a : R, (K * M') *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have yx : sqf c J y x = 1 := by rw [sqf_symm c hc J hJ, xy, map_one]
  have xo : ∀ u, sqf c J x (ι *ᵥ u) = 0 := fun u => by rw [sqf_symm c hc J hJ, ox, map_zero]
  have yo : ∀ u, sqf c J y (ι *ᵥ u) = 0 := fun u => by rw [sqf_symm c hc J hJ, oy, map_zero]
  have vv : ∀ a b z : Fin n → R, Matrix.vecMulVec a (J *ᵥ fun i => c (b i)) *ᵥ z = sqf c J z b • a := fun a b z => by
    rw [Matrix.vecMulVec_mulVec, sqf, dotProduct_comm]
    funext i; simp [mul_comm]
  have dec : ∀ z, z = ι *ᵥ (π *ᵥ z) + sqf c J z y • x + sqf c J z x • y := fun z => by
    rw [← vv, ← vv, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, q2, Matrix.one_mulVec]
  have pi : ∀ u, π *ᵥ (ι *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, q1, Matrix.one_mulVec]
  have px : π *ᵥ x = 0 := by
    have h := dec x
    rw [xy, xx, one_smul, zero_smul, add_zero, right_eq_add] at h
    rw [← pi (π *ᵥ x), h, Matrix.mulVec_zero]
  have py : π *ᵥ y = 0 := by
    have h := dec y
    rw [yx, yy, one_smul, zero_smul, add_zero, right_eq_add] at h
    rw [← pi (π *ᵥ y), h, Matrix.mulVec_zero]
  have fm : ∀ u u' (a b a' b' : R), sqf c J (ι *ᵥ u + a • x + b • y) (ι *ᵥ u' + a' • x + b' • y) =
      sqf c J₁ u u' + a * c b' + b * c a' := fun u u' a b a' b' => by
    simp only [sqf_add_left, sqf_add_right, sqf_smul_left, sqf_smul_right, ox, oy, xo, yo, xx, yy, xy, yx, sqf_mul, gram]
    ring
  have hx' : K' *ᵥ x = (t⁻¹).1 • x := by
    have := congrArg (fun z => (t⁻¹).1 • (K' *ᵥ z)) hx
    simp only [Matrix.mulVec_mulVec, hK', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm
  have st : ∀ (L : Matrix (Fin n) (Fin n) R) (s : Rˣ), Lᵀ * J * L.map c = J → L *ᵥ x = s.1 • x → ∀ u, ∃ a : R,
      L *ᵥ (ι *ᵥ u) = ι *ᵥ ((π * L * ι) *ᵥ u) + a • x := fun L s hL hs u => by
    have h0 : sqf c J (L *ᵥ (ι *ᵥ u)) x = 0 := by
      have h1 := sqf_mul c J L (ι *ᵥ u) x
      rw [hL, ox, hs, sqf_smul_right] at h1
      exact (s.isUnit.map c).mul_right_eq_zero.1 h1
    refine ⟨sqf c J (L *ᵥ (ι *ᵥ u)) y, ?_⟩
    conv_lhs => rw [dec (L *ᵥ (ι *ᵥ u)), h0]
    simp only [zero_smul, add_zero, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have iv : ∀ (L L' : Matrix (Fin n) (Fin n) R) (s s' : Rˣ), L * L' = 1 → L'ᵀ * J * L'.map c = J → L *ᵥ x = s.1 • x →
      L' *ᵥ x = s'.1 • x → π * L * ι * (π * L' * ι) = 1 := fun L L' s s' h1 h2 h3 h4 => by
    refine mat_ext fun u => ?_
    obtain ⟨a, ha⟩ := st L' s' h2 h4 u
    have h5 := congrArg (fun z => π *ᵥ (L *ᵥ z)) ha
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h3, px, smul_zero, add_zero] at h5
    rw [Matrix.mulVec_mulVec (ι *ᵥ u) L L', h1, Matrix.one_mulVec, pi] at h5
    rw [Matrix.one_mulVec]
    conv_rhs => rw [h5]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have g1 := iv K K' t t⁻¹ hK hu' hx hx'
  have g2 := iv K' K t⁻¹ t hK' hu hx' hx
  have gK := st K t hu hx
  generalize π * K * ι = G at g1 g2 gK ⊢
  generalize π * K' * ι = G' at g1 g2
  have gu : ∀ u u', sqf c J₁ (G *ᵥ u) (G *ᵥ u') = sqf c J₁ u u' := fun u u' => by
    obtain ⟨a, ha⟩ := gK u
    obtain ⟨a', ha'⟩ := gK u'
    have h1 := fm (G *ᵥ u) (G *ᵥ u') a 0 a' 0
    simp only [zero_smul, add_zero, map_zero, mul_zero, zero_mul] at h1
    rw [← h1, ← ha, ← ha', sqf_mul, hu, sqf_mul, gram]
  have lev : ∀ (D : Matrix (Fin m) (Fin m) R) (p q : R), ∃ M : Matrix (Fin n) (Fin n) R, ∀ u (a b : R),
      M *ᵥ (ι *ᵥ u + a • x + b • y) = ι *ᵥ (D *ᵥ u) + (p * a) • x + (q * b) • y := fun D p q => by
    refine ⟨ι * D * π + p • Matrix.vecMulVec x (J *ᵥ fun i => c (y i)) +
      q • Matrix.vecMulVec y (J *ᵥ fun i => c (x i)), fun u a b => ?_⟩
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vv, vv, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [sqf_add_left, sqf_smul_left, ox, oy, xx, yy, xy, yx, Matrix.mulVec_add, Matrix.mulVec_smul, pi, px, py,
      smul_zero, add_zero, zero_add, mul_zero, mul_one, smul_smul]
  obtain ⟨M, hM⟩ := lev G t.1 (c (t⁻¹).1)
  obtain ⟨M', hM'⟩ := lev G' (t⁻¹).1 (c t.1)
  have c1 : c t.1 * c (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have c2 : c (t⁻¹).1 * c t.1 = 1 := by rw [mul_comm, c1]
  refine ⟨G', M, M', g1, g2, sqf_ext c _ _ fun u u' => by rw [← sqf_mul, gu], mat_ext fun z => ?_, mat_ext fun z => ?_,
    sqf_ext c _ _ fun z z' => ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dec z, hM', hM, Matrix.mulVec_mulVec _ G, g1, Matrix.one_mulVec,
      ← mul_assoc, ← mul_assoc, Units.mul_inv, c2, one_mul, one_mul]
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dec z, hM, hM', Matrix.mulVec_mulVec _ G', g2, Matrix.one_mulVec,
      ← mul_assoc, ← mul_assoc, Units.inv_mul, c1, one_mul, one_mul]
  · rw [← sqf_mul, dec z, dec z', hM, hM, fm, fm, gu, map_mul, map_mul, hc]
    linear_combination (sqf c J z y * c (sqf c J z' x)) * t.mul_inv + (sqf c J z x * c (sqf c J z' y)) * c1
  · simpa using hM 0 1 0
  · simpa using hM 0 0 1
  · ext i j
    have h := congrFun (hM (Pi.single j 1) 0 0) i
    simp only [zero_smul, add_zero, mul_zero, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  · have h := hM' 0 1 0
    simp only [Matrix.mulVec_zero, zero_add, one_smul, zero_smul, add_zero, mul_one, mul_zero] at h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul]
  · have h := hM' z 0 0
    simp only [zero_smul, add_zero, mul_zero] at h
    obtain ⟨a, ha⟩ := gK (G' *ᵥ z)
    exact ⟨a, by rw [← Matrix.mulVec_mulVec, h, ha, Matrix.mulVec_mulVec _ G, g1, Matrix.one_mulVec]⟩

end SlopeTestRemainingChoices
