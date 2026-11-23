module

public import Development.EtaleCohomology.DivisorCycles.CycleCountPf
public import Development.EtaleCohomology.DivisorCycles.AlgStruct2
public import Development.EtaleCohomology.DivisorCycles.ChainPf
public import Development.EtaleCohomology.DivisorCycles.OpenCoset
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
public import Development.EtaleCohomology.DivisorCycles.CycSpecQzkPf
public import Development.EtaleCohomology.DivisorCycles.DegPoly2
public import Development.EtaleCohomology.DivisorCycles.DiagScalar2
public import Development.EtaleCohomology.DivisorCycles.ExpVanPf
public import Development.EtaleCohomology.DivisorCycles.FixScalOf
public import Development.EtaleCohomology.DivisorCycles.GradePf
public import Development.EtaleCohomology.DivisorCycles.CycleCount
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Development.EtaleCohomology.DivisorCycles.SemisPf
public import Mathlib.RingTheory.Derivation.Lie
public import Development.EtaleCohomology.DivisorCycles.TangentDegree
public import Development.EtaleCohomology.DivisorCycles.TangentFieldExtension

-- Source module: Development.EtaleCohomology.DivisorCycles.CoeMulInv

section

@[expose] public section

open Matrix

namespace LateralTheory.DivDb.EnvStab₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N : ℕ}

theorem ev_X (x : Mat C N) (q : Fin N × Fin N) : ev x (MvPolynomial.X q) = x q.1 q.2 := by
  simp [ev]

theorem mem_img (ρ : Γ →* GL (Fin N) C) (h : Γ) : ((ρ h : GL (Fin N) C) : Mat C N) ∈ (img ρ ⊤ : Set (Mat C N)) := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map]
  exact ⟨h, by simp, rfl⟩

theorem img_cases (ρ : Γ →* GL (Fin N) C) {x : Mat C N} (hx : x ∈ (img ρ ⊤ : Set (Mat C N))) :
    ∃ h : Γ, ((ρ h : GL (Fin N) C) : Mat C N) = x := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map] at hx
  obtain ⟨h, _, rfl⟩ := hx
  exact ⟨h, rfl⟩

theorem coe_mul_inv (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem coe_inv_mul (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) * ((ρ g : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

def conjL (G G' : Mat C N) : Mat C N →ₗ[C] Mat C N where
  toFun x := G * x * G'
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp

theorem lie_conj (hC : Chain) (ρ : Γ →* GL (Fin N) C) (g : Γ) (Y : Mat C N) (hY : Y ∈ lie ρ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * Y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ lie ρ := by
  intro f hf
  obtain ⟨f', hev, hd⟩ := hC C N N (conjL (ρ g : Mat C N) (ρ g⁻¹ : Mat C N)) f
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev]
    apply hf
    have : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) (ρ h : Mat C N)
        = ((ρ (g * h * g⁻¹) : GL (Fin N) C) : Mat C N) := by
      simp [conjL, map_mul, Units.val_mul]
    rw [this]; exact mem_img ρ _
  have h1 : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) 1 = 1 := by
    simp only [conjL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_one]; exact coe_mul_inv ρ g
  have := hd 1 Y
  rw [h1] at this
  show dAt f 1 (conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) Y) = 0
  rw [← this]
  exact hY f' hf'

theorem normd (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Normd ρ (env ρ) := by
  intro g a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (lie_conj hC ρ g x hx)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, coe_mul_inv]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) r
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have : ((ρ g : GL (Fin N) C) : Mat C N) * (x * y) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)
        = (((ρ g : GL (Fin N) C) : Mat C N) * x * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) *
          (((ρ g : GL (Fin N) C) : Mat C N) * y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((ρ g⁻¹ : GL (Fin N) C) : Mat C N), coe_inv_mul, Matrix.one_mul]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

def lamL (ℓ : Module.Dual C (Fin N → C)) (v : Fin N → C) : Mat C N →ₗ[C] Mat C 1 where
  toFun x := Matrix.of fun _ _ => ℓ (x *ᵥ v)
  map_add' x y := by ext; simp [Matrix.add_mulVec]
  map_smul' c x := by ext; simp [Matrix.smul_mulVec]

theorem lie_keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) (W : Submodule C (Fin N → C))
    (hW : ∀ g, ∀ v ∈ W, ((ρ g : GL (Fin N) C) : Mat C N) *ᵥ v ∈ W) (Y : Mat C N) (hY : Y ∈ lie ρ)
    (v : Fin N → C) (hv : v ∈ W) : Y *ᵥ v ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  rw [Submodule.mem_dualAnnihilator] at hℓ
  obtain ⟨f', hev, hd⟩ := hC C N 1 (lamL ℓ v) (MvPolynomial.X (0, 0))
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev, ev_X]
    simp only [lamL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    exact hℓ _ (hW h v hv)
  have h0 := hY f' hf'
  rw [hd] at h0
  simpa [dAt, lamL, ev, MvPolynomial.pderiv_X, Fintype.sum_unique, Pi.single_apply, Prod.ext_iff, Fin.fin_one_eq_zero] using h0

theorem keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Keeps ρ (env ρ) := by
  intro W hW a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact fun v hv => lie_keeps hC ρ W hW x hx v hv
  | algebraMap r =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem r hv
  | add x y _ _ hx hy =>
    intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv; rw [← Matrix.mulVec_mulVec]; exact hx _ (hy v hv)

end LateralTheory.DivDb.EnvStab₂

namespace LateralTheory.DivDb

theorem EnvStab_of (hC : Chain) : EnvStab := fun _ _ _ _ _ ρ =>
  ⟨EnvStab₂.normd hC ρ, EnvStab₂.keeps hC ρ⟩

end LateralTheory.DivDb
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.ProjPf

section

@[expose] public section

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ProjPf

variable {C : Type} [Field C] {N n : ℕ}

theorem root_minpoly (X : LateralTheory.DivDb.Mat C N) (c : C) (h : X.charpoly.IsRoot c) :
    (minpoly C X).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)
  rw [← Matrix.minpoly_toLin']
  exact Module.End.hasEigenvalue_iff_isRoot.1 h1

theorem prod_dvd (e : Fin n → C) (he : Function.Injective e) (f : C[X]) (hf : ∀ k, f.eval (e k) = 0) :
    (∏ k, (X - Polynomial.C (e k))) ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · exact fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab
  · intro k _; exact Polynomial.dvd_iff_isRoot.2 (hf k)

theorem minpoly_eq (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) :
    minpoly C X = ∏ k, (Polynomial.X - Polynomial.C (e k)) := by
  obtain ⟨q, hq0, hqd, hq⟩ := hD
  have hint : IsIntegral C X := Matrix.isIntegral X
  have hmon : (minpoly C X).Monic := minpoly.monic hint
  have hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X :=
    prod_dvd e he _ (fun k => root_minpoly X _ (hr k))
  have hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdeg : (minpoly C X).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0
    omega
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hdeg

theorem evb (e : Fin n → C) (he : Function.Injective e) (i k : Fin n) :
    (Lagrange.basis Finset.univ e i).eval (e k) = if k = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)

theorem vanish (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) (f : C[X])
    (hf : ∀ k, f.eval (e k) = 0) : aeval X f = 0 := by
  rw [← minpoly.dvd_iff, minpoly_eq X e he hD hr]
  exact prod_dvd e he f hf

end LateralTheory.DivDb.ProjPf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.ProjPf

theorem Proj_of : Proj := by
  intro C _ N n X e he hD hr
  classical
  set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb
  have V := vanish X e he hD hr
  refine ⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩
  · show aeval X (b i) * aeval X (b i) = aeval X (b i)
    rw [← sub_eq_zero, ← map_mul, ← map_sub]
    apply V; intro k
    simp only [hb, eval_sub, eval_mul, evb e he]
    split_ifs <;> simp
  · show aeval X (b i) * aeval X (b j) = 0
    rw [← map_mul]
    apply V; intro k
    simp only [hb, eval_mul, evb e he]
    split_ifs with h1 h2 <;> simp_all
  · show ∑ i, aeval X (b i) = 1
    have h : aeval X (∑ i, b i - 1) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]
      simp

    rw [map_sub, map_one, map_sum, sub_eq_zero] at h
    exact h
  · intro h0
    have h1 : minpoly C X ∣ b i := (minpoly.dvd_iff).2 h0
    rw [minpoly_eq X e he hD hr] at h1
    have hne : b i ≠ 0 := Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)] at h2
    have h3 : (b i).natDegree = n - 1 := by
      simp only [hb]
      rw [Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]
      simp
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h2
    have := i.pos
    omega
  · have : aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]
      simp

    rw [map_sub, aeval_X, map_sum, sub_eq_zero] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, aeval_C, Algebra.smul_def]
  · exact Polynomial.aeval_mem_adjoin_singleton C _

end LateralTheory.DivDb
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.StructPf

section

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.TanLiePf

section

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]

  simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.FinStruct

section

@[expose] public section

namespace LateralTheory.Fin.Struct
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_projection_system_of_structure : LateralTheory.DivDb.Proj := by
  apply LateralTheory.DivDb.Proj_of
theorem etale_tangent_lie_algebra_of_structure : LateralTheory.DivDb.TanLie := by
  apply LateralTheory.DivDb.TanLie_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_cyclic_grading_of_structure : LateralTheory.DivDb.Grade := by
  apply LateralTheory.DivDb.Grade_of
theorem etale_cycle_spectrum_of_structure : LateralTheory.DivDb.CycleCountPf.CycSpec := by
  apply LateralTheory.DivDb.CycSpec_qzkPf.CycSpec_of
theorem etale_fixed_cycle_scalar_of_structure : LateralTheory.DivDb.CycleCountPf.FixScal := by
  apply LateralTheory.DivDb.ScalarFixedPointsUnderAeval.FixScal_of
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCountPf.CycleCount_of <;> first | exact etale_cycle_spectrum_of_structure | exact etale_fixed_cycle_scalar_of_structure
theorem etale_diagonal_scalar_of_structure : LateralTheory.DivDb.DiagScalar := by
  apply LateralTheory.DivDb.DiagScalar_of <;> first | exact etale_cycle_count_eigenvalues_of_key
theorem etale_algebra_decomposition_of_structure : LateralTheory.DivDb.AlgStruct := by
  apply LateralTheory.DivDb.AlgStruct₂.AlgStruct_of
theorem etale_envelope_stabilizer_of_structure : LateralTheory.DivDb.EnvStab := by
  apply LateralTheory.DivDb.EnvStab_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem etale_algebra_structure_theorem_of_components : LateralTheory.DivDb.Struct := by
  apply LateralTheory.DivDb.StructPf.Struct_of <;> first | exact etale_tangent_degree_bound_of_key | exact etale_projection_system_of_structure | exact etale_tangent_lie_algebra_of_structure | exact etale_cyclic_grading_of_structure | exact etale_diagonal_scalar_of_structure | exact etale_algebra_decomposition_of_structure | exact etale_envelope_stabilizer_of_structure | exact etale_semisimplicity_instance
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Struct := etale_algebra_structure_theorem_of_components
end LateralTheory.Fin.Struct
end
end
