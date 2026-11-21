module

public import Mathlib

@[expose] public section


open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def IsBlockUT {ι : Type} {s : ℕ} (b : ι → Fin s) (M : Matrix ι ι K) : Prop :=
  ∀ i j, b j < b i → M i j = 0

variable {K} in
theorem isBlockUT_mul {ι : Type} [Fintype ι] {s : ℕ} (b : ι → Fin s) {A B : Matrix ι ι K}
    (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) : IsBlockUT K b (A * B) := by
  intro i j h
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : b k < b i
  · simp [hA i k hk]
  · simp [hB k j (lt_of_lt_of_le h (not_lt.mp hk))]

def parab {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := {g | IsBlockUT K b (g : Matrix ι ι K) ∧ IsBlockUT K b ((g⁻¹ : GL ι K) : Matrix ι ι K)}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;>
    · intro i j h
      have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne hij]
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨?_, ?_⟩
    · simpa [Units.val_mul] using isBlockUT_mul b hg hh
    · simpa [mul_inv_rev, Units.val_mul] using isBlockUT_mul b hh' hg'
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨hg', by simpa using hg⟩

def unip {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Set (GL ι K) :=
  {g | g ∈ parab K b ∧ ∀ i j, b i = b j → (g : Matrix ι ι K) i j = if i = j then 1 else 0}

def IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  ∀ (s : ℕ) (b : ι → Fin s), Function.Surjective b → 2 ≤ s →
    ∀ v : τ, (∀ u ∈ unip K b, τ.ρ u v = v) → v = 0

def blk {ι : Type} {s : ℕ} (b : ι → Fin s) (c : Fin s) (M : Matrix ι ι K) :
    Matrix {i // b i = c} {i // b i = c} K :=
  M.submatrix Subtype.val Subtype.val

variable {K} in
theorem blk_mul {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    {A B : Matrix ι ι K} (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) :
    blk K b c (A * B) = blk K b c A * blk K b c B := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = c)]
  have h0 : ∑ k : {k // ¬ b k = c}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ _
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k (by rw [hi]; exact h)]; simp
    · rw [hB k j (by rw [hj]; exact h)]; simp
  rw [h0, add_zero]

def levi {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    (p : parab K b) : GL {i // b i = c} K :=
  ⟨blk K b c (p.1 : Matrix ι ι K), blk K b c ((p.1⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← blk_mul b c p.2.1 p.2.2, Units.mul_inv]; exact Matrix.submatrix_one _ Subtype.val_injective,
    by rw [← blk_mul b c p.2.2 p.2.1, Units.inv_mul]; exact Matrix.submatrix_one _ Subtype.val_injective⟩

section HC
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def infl (p : parab K b) :
    PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] PiTensorProduct ℂ (fun c => (lam c : Type)) :=
  PiTensorProduct.map (fun c => (lam c).ρ (levi K b c p))

def hcSpace : Submodule ℂ (GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) where
  carrier := {f | ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)}
  add_mem' := by
    intro f g hf hg p x
    simp [hf p x, hg p x]
  zero_mem' := by
    intro p x
    simp
  smul_mem' := by
    intro a f hf p x
    simp [hf p x]

def hcRep : Representation ℂ (GL ι K) (hcSpace K b lam) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (x * g), fun p x => by simpa [mul_assoc] using f.2 p (x * g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    ext f x
    simp
  map_mul' := by
    intro g h
    ext f x
    simp [mul_assoc]
end HC

section Reps
variable {Γ : Type} [Group Γ]

def Intw {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ V') : Submodule ℂ (V →ₗ[ℂ] V') where
  carrier := {φ | ∀ g, φ ∘ₗ ρ g = ρ' g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro a φ hφ g
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

def IsConstituent {V : Type} [AddCommGroup V] [Module ℂ V] (τ : FDRep ℂ Γ)
    (ρ : Representation ℂ Γ V) : Prop :=
  ∃ φ ∈ Intw τ.ρ ρ, φ ≠ 0

def IsIrrRep {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))
end Reps

structure LabelConv where
  ι : AlgebraicClosure K →* ℂ
  ι_inj : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → ι x = ι y → x = y
  gen : ℕ → AlgebraicClosure K
  gen_order : ∀ d, 1 ≤ d → orderOf (gen d) = Fintype.card K ^ d - 1
  gen_norm : ∀ d e, 1 ≤ d → 1 ≤ e →
    gen (d * e) ^ ((Fintype.card K ^ (d * e) - 1) / (Fintype.card K ^ d - 1)) = gen d

def rootsBar (f : K[X]) : Multiset (AlgebraicClosure K) :=
  (f.map (algebraMap K (AlgebraicClosure K))).roots

variable {K} in

def HasCuspLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (P : K[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = Fintype.card ι ∧
    ∀ x : AlgebraicClosure K, aeval x P = 0 →
    ∀ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) →
    ∀ z : AlgebraicClosure K, aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0 →
    ∀ m : ℕ, C.gen (Fintype.card ι) ^ m = z →
      LinearMap.trace ℂ τ (τ.ρ γ) =
        (-1) ^ (Fintype.card ι - 1) *
          ∑ a ∈ Finset.range (Fintype.card ι), C.ι x ^ (m * Fintype.card K ^ a)

variable {K} in

def HasLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (P : Fin s → K[X]),
    Function.Surjective b ∧
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) ∧ HasCuspLabel C (lam c) (P c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, P c

abbrev q : ℕ := Fintype.card K

def CuspParam (C : LabelConv K) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ τ : FDRep ℂ (GL (Fin d) K), Simple τ → IsCuspidal K τ →
      (∃! P : K[X], HasCuspLabel C τ P) ∧
      (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1)) ∧
    (∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
      ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P) ∧
    (∀ (τ τ' : FDRep ℂ (GL (Fin d) K)) (P : K[X]), Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      HasCuspLabel C τ P → HasCuspLabel C τ' P → Nonempty (τ ≅ τ'))

end Formalism.IrreducibleCountingLemmas.TYPES

open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def glEquiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv


def transp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (τ : FDRep ℂ (GL ι K)) : FDRep ℂ (GL κ K) :=
  FDRep.of (τ.ρ.comp (glEquiv K e).symm.toMonoidHom)

structure LabelMap (C : LabelConv K) where
  lab : ∀ d : ℕ, FDRep ℂ (GL (Fin d) K) → K[X]
  lab_iso : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), Nonempty (τ ≅ τ') → lab d τ = lab d τ'
  lab_spec : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    (lab d τ).Monic ∧ Irreducible (lab d τ) ∧ lab d τ ≠ X ∧ (lab d τ).natDegree = d
  lab_inj : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' → lab d τ = lab d τ' → Nonempty (τ ≅ τ')
  lab_one : ∀ (τ : FDRep ℂ (GL (Fin 1) K)) (x : K), Simple τ → x ≠ 0 →
    (∀ (γ : GL (Fin 1) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m) →
    lab 1 τ = X - Polynomial.C x


def LabelMapEquivariant {C : LabelConv K} (O : LabelMap K C) : Prop :=
  (∀ (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ τ τ' : FDRep ℂ (GL (Fin d) K), 1 ≤ d → Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) →
      rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· ^ a)) ∧
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' →
    (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (·⁻¹)

variable {K} {C : LabelConv K}

def labO (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] (σ : FDRep ℂ (GL κ K)) : K[X] :=
  O.lab (Fintype.card κ) (transp K (Fintype.equivFin κ) σ)

def HasLabelO (O : LabelMap K C) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, labO O (lam c)

def DisjointMultO (O : LabelMap K C) : Prop :=
  ∀ (n : ℕ) (b : Fin n → Fin 2) (τ σ : ∀ c : Fin 2, FDRep ℂ (GL {i // b i = c} K)) (f f' : Fin 2 → K[X]),
    Function.Surjective b →
    (∀ c, Simple (τ c) ∧ Simple (σ c) ∧ HasLabelO O (τ c) (f c) ∧ HasLabelO O (σ c) (f' c)) →
    IsCoprime (f 0) (f' 1) → IsCoprime (f 1) (f' 0) →
    Module.finrank ℂ (Intw (hcRep K b τ) (hcRep K b σ)) =
      Module.finrank ℂ (Intw (τ 0).ρ (σ 0).ρ) * Module.finrank ℂ (Intw (τ 1).ρ (σ 1).ρ)



def twoBlock (n a : ℕ) : Fin n → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1




def ZIdemOccurs : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Simple τ →
    ((∃ v : V, ρ.asAlgebraHom (zIdem τ) v ≠ 0) ↔ IsConstituent τ ρ)

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

section BaseChange
variable {Γ : Type} [Group Γ]

def bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) : Representation ℂ Γ (Fin (Module.finrank ℂ V) → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ ≃ₐ[ℂ]
      ((Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))).toRingEquiv.toMonoidHom.comp
    ((σ.toRingHom.mapMatrix : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →+*
        Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toRingEquiv.toMonoidHom.comp ρ))

def bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : FDRep ℂ Γ := FDRep.of (bcRepr σ τ.ρ)

theorem trace_bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) (γ : Γ) :
    LinearMap.trace ℂ _ (bcRepr σ ρ γ) = σ (LinearMap.trace ℂ V (ρ γ)) := by
  have h1 : bcRepr σ ρ γ = Matrix.toLin' (σ.toRingHom.mapMatrix
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ γ))) := rfl
  rw [h1, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ γ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem finrank_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) :
    Module.finrank ℂ (bc σ τ) = Module.finrank ℂ τ := by
  exact Module.finrank_fin_fun ℂ

theorem zIdem_coeff [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ) :
    (zIdem τ).coeff γ = (Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹) := by
  classical
  unfold zIdem
  simp [MonoidAlgebra.coeff, Finsupp.finsetSum_apply, Finsupp.single_apply, MonoidAlgebra.single]
end BaseChange

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def BcZIdem : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ),
    σ ((zIdem τ).coeff γ) = (zIdem (bc σ τ)).coeff γ

theorem galoisConjCentralIdempotent : BcZIdem := by
  intro Γ _ _ σ τ γ
  have h : LinearMap.trace ℂ (bc σ τ) ((bc σ τ).ρ γ⁻¹) = σ (LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :=
    trace_bcRepr σ τ.ρ γ⁻¹
  rw [zIdem_coeff, zIdem_coeff, finrank_bc, h, map_mul, map_div₀, map_natCast, map_natCast]

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

end Formalism.IrreducibleCountingLemmas.TYPES
