module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsIntegralVecCoordsOfMemAdelicLatticeOne
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicSplit
import GroundTheory.AutomorphicForms.HermitianOrthogonal
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
public import Mathlib.GroupTheory.IndexNSmul
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices
import Mathlib.RingTheory.PiTensorProduct

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.RelIndexNeZeroAndLeOfNsmulMem

section

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

section Index

theorem relIndex_ne_zero_and_le_of_nsmul_mem {W : Type*} [AddCommGroup W]
    [Module.IsTorsionFree ℤ W] {L P : AddSubgroup W} {Q : Submodule ℤ W} [Module.Finite ℤ Q]
    (hLP : L ≤ P) (hPQ : P.toIntSubmodule ≤ Q) {n : ℕ} (hn : n ≠ 0) (hnL : ∀ y ∈ P, n • y ∈ L) :
    L.relIndex P ≠ 0 ∧ L.relIndex P ≤ n ^ finrank ℤ Q := by
  haveI : Module.Finite ℤ P.toIntSubmodule :=
    Module.Finite.of_injective (Submodule.inclusion hPQ) (Submodule.inclusion_injective hPQ)
  have key := AddSubgroup.relIndex_map_nsmul n P
  have hle : P.map (nsmulAddMonoidHom (α := W) n) ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnL y hy
  have hne : (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hn
  have hrank : finrank ℤ P.toIntSubmodule ≤ finrank ℤ Q := Submodule.finrank_mono hPQ
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hle h0), ?_⟩
  calc L.relIndex P ≤ (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P :=
        AddSubgroup.relIndex_le_of_le_left hle hne
    _ = n ^ finrank ℤ P.toIntSubmodule := key
    _ ≤ n ^ finrank ℤ Q := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hrank

end Index

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Coordinates


variable (F) in
def coordEquiv (v : Basis ι E W) : W ≃+ (ι → F ⊗[F] E) :=
  v.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (Algebra.TensorProduct.lid F E).symm.toAddEquiv)

theorem coordEquiv_apply (v : Basis ι E W) (x : W) (i : ι) :
    coordEquiv F v x i = (1 : F) ⊗ₜ[F] v.repr x i := by
  simp [coordEquiv, Algebra.TensorProduct.lid_symm_apply]

theorem coordEquiv_smul (v : Basis ι E W) (e : E) (x : W) :
    coordEquiv F v (e • x) = ((1 : F) ⊗ₜ[F] e) • coordEquiv F v x := by
  funext i
  simp only [coordEquiv_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, map_smul, Finsupp.smul_apply]

theorem pairE_coordEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x y : W) :
    pairE (gram h.toSesq v) (coordEquiv F v x) (coordEquiv F v y) = h.toSesq x y := by
  rw [sesq_eq_sum h.toSesq v x y, pairE, hermPair]
  simp only [dotProduct, mulVec, baseMatrix, Matrix.map_apply, coordEquiv_apply, conjBase_tmul,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Finset.mul_sum, ← TensorProduct.tmul_sum, Algebra.TensorProduct.lid_tmul, one_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecCoords_coordEquiv {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W) (x : W)
    (i : ι) (k : κ) : vecCoords F b (coordEquiv F v x) (i, k) = b.repr (v.repr x i) k := by
  rw [vecCoords, coordEquiv_apply, repr_one_tmul, Algebra.algebraMap_self, RingHom.id_apply]

end Coordinates

section Equivariance

variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem mulVec_coordEquiv (γ : h.unitaryGroup) (y : W) :
    unitaryMat ((unitaryPointsRationalEquivHermitian F E h v).symm γ) *ᵥ coordEquiv F v y =
      coordEquiv F v ((γ : W ≃ₗ[E] W) y) := by
  set γ' := (unitaryPointsRationalEquivHermitian F E h v).symm γ
  have h1 : unitaryPointsRationalEquiv F E (gram h.toSesq v) γ' = unitaryGroupEquivMatrix h v γ := by
    show unitaryPointsRationalEquiv F E _ (((unitaryPointsRationalEquiv F E _).trans
      (unitaryGroupEquivMatrix h v).symm).symm γ) = _
    rw [MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  have hM : (unitaryMat γ').map (Algebra.TensorProduct.lid F E) =
      LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [← unitaryGroupEquivMatrix_apply, ← h1]
    rfl
  funext i
  apply (Algebra.TensorProduct.lid F E).injective
  rw [coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul,
    show v.repr ((γ : W ≃ₗ[E] W) y) = v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) y) from rfl,
    ← LinearMap.toMatrix_mulVec_repr v v, ← hM]

  simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, coordEquiv_apply,
  Algebra.TensorProduct.lid_tmul, one_smul]

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem adeleSplit_snd_hermitianDiagonal (γ : h.unitaryGroup) :
    (adeleSplit h v (hermitianDiagonal h v γ)).2 =
      finDiag (gram h.toSesq v) ((unitaryPointsRationalEquivHermitian F E h v).symm γ) := by
  apply unitaryCoords_injective _ _ (Module.finBasis F E)
  funext p
  simp [adeleSplit, unitaryCongr_apply, hermitianDiagonal, unitaryDiagonal, finDiag,
    unitaryCoords_unitaryMap, adeleRingEquivProd]
  have hprod (x : unitaryPoints F E (gram h.toSesq v)
      (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :
      (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v) x).2 =
        unitaryMap F E _ (AlgHom.snd F _ _) x := rfl
  rw [hprod]
  simp only [unitaryCoords_unitaryMap, Function.comp_apply]
  rfl

end Equivariance

section Lattice

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

def dictLattice (d : ℤ) (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) : AddSubgroup W :=
  (coreLattice b (gram h.toSesq v) g).comap
    ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp (DistribSMul.toAddMonoidHom W ((d : E)⁻¹)))

variable {b h v}

theorem mem_dictLattice {d : ℤ} {g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} {x : W} :
    x ∈ dictLattice b h v d g ↔ coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g :=
  Iff.rfl

theorem dictLattice_eq_iff {d : ℤ} (hd : d ≠ 0) {g g' : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} :
    dictLattice b h v d g = dictLattice b h v d g' ↔ g⁻¹ * g' ∈ coreStabilizer b (gram h.toSesq v) := by
  rw [← coreLattice_eq_iff b]
  have hsurj : Function.Surjective ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp
      (DistribSMul.toAddMonoidHom W ((d : E)⁻¹))) := by
    intro X
    refine ⟨(d : E) • (coordEquiv F v).symm X, ?_⟩
    show coordEquiv F v ((d : E)⁻¹ • ((d : E) • (coordEquiv F v).symm X)) = X
    rw [inv_smul_smul₀ (by exact_mod_cast hd), AddEquiv.apply_symm_apply]
  exact (AddSubgroup.comap_injective hsurj).eq_iff

theorem mem_smul_addSubgroup_iff (γ : h.unitaryGroup) (S : AddSubgroup W) (x : W) :
    x ∈ γ • S ↔ γ⁻¹ • x ∈ S := by
  exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem dictLattice_diagonal_mul (d : ℤ) (γ : h.unitaryGroup)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    dictLattice b h v d ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • dictLattice b h v d g := by
  ext x
  rw [mem_smul_addSubgroup_iff, mem_dictLattice, mem_dictLattice, adeleSplit_snd_hermitianDiagonal,
    ← mulVec_mem_coreLattice_iff b ((unitaryPointsRationalEquivHermitian F E h v).symm γ) g,
    mulVec_coordEquiv]
  have : ((γ : W ≃ₗ[E] W) ((d : E)⁻¹ • (γ⁻¹ • x))) = (d : E)⁻¹ • x := by
    rw [map_smul]
    congr 1
    show (γ : W ≃ₗ[E] W) (((γ⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) x) = x
    rw [Subgroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ x
  rw [this]

end Lattice

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary

section

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Span

variable {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W)

def coordSpan (c : F) : (ι × κ → 𝓞 F) →ₗ[ℤ] W :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun z => ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1
      map_zero' := by simp
      map_add' := fun z z' => by
        simp only [Pi.add_apply, map_add (f := _), mul_add, add_mul, add_smul, Finset.sum_add_distrib] }

theorem mem_range_coordSpan {c : F} (hc : c ≠ 0) {x : W}
    (hx : ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k)) :
    x ∈ LinearMap.range (coordSpan b v c) := by
  choose z hz using fun a : ι × κ =>
    (⟨⟨_, hx a.1 a.2⟩, rfl⟩ : ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c * b.repr (v.repr x a.1) a.2)
  refine ⟨z, ?_⟩
  show ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1 = x
  simp only [hz, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← b.sum_repr (v.repr x i)]
  simp only [Algebra.smul_def]

end Span

theorem isTorsionFree_int_of_module (K' V' : Type*) [Field K'] [CharZero K'] [AddCommGroup V']
    [Module K' V'] : Module.IsTorsionFree ℤ V' :=
  Module.IsTorsionFree.comap (S := K') (fun n : ℤ => (n : K'))
    (fun r hr => isRegular_iff_ne_zero.2 (Int.cast_ne_zero.2 (isRegular_iff_ne_zero.1 hr)))
    (fun r m => Int.cast_smul_eq_zsmul K' r m)

section DIntegral

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

theorem repr_repr_smul_inv_int (d : ℤ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr ((d : E)⁻¹ • x) i) k = (d : F)⁻¹ * b.repr (v.repr x i) k := by
  have : (d : E)⁻¹ = algebraMap F E (d : F)⁻¹ := by rw [map_inv₀, map_intCast]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, this, ← Algebra.smul_def, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem repr_repr_nsmul (n : ℕ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr (n • x) i) k = n * b.repr (v.repr x i) k := by
  rw [map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem isDIntegral_dictLattice {d : ℤ} (hd0 : d ≠ 0)
    (hd : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (x y : ι → F ⊗[F] E),
      x ∈ coreLattice b (gram h.toSesq v) g → y ∈ coreLattice b (gram h.toSesq v) g →
        IsIntegral ℤ ((d : E) * pairE (gram h.toSesq v) x y))
    {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (y : ι → F ⊗[F] E),
      (∀ x ∈ coreLattice b (gram h.toSesq v) g, IsIntegral ℤ (pairE (gram h.toSesq v) y x)) →
        (m : F) • y ∈ coreLattice b (gram h.toSesq v) g)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    IsDIntegral h ((m * d * d).natAbs ^ finrank ℤ (ι × κ → 𝓞 F)) (dictLattice b h v d g) := by
  classical
  haveI : Module.IsTorsionFree ℤ W := isTorsionFree_int_of_module E W
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hsmulL : ∀ (c : E) (x y : W), h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
    intro c x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  have hsmulR : ∀ (c : E) (x y : W), h.toSesq x (c • y) = c * h.toSesq x y := by
    intro c x y
    rw [map_smul, smul_eq_mul]
  have hconjd : conj F E (d : E) = d := map_intCast _ _
  have hdI : IsIntegral ℤ (d : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := d))

  have hint : ∀ x ∈ dictLattice b h v d g, ∀ y ∈ dictLattice b h v d g, IsIntegral ℤ (h.toSesq x y) := by
    intro x hx y hy
    have e : h.toSesq x y = (d : E) * ((d : E) * pairE (gram h.toSesq v) (coordEquiv F v ((d : E)⁻¹ • x))
        (coordEquiv F v ((d : E)⁻¹ • y))) := by
      rw [pairE_coordEquiv, hsmulL, hsmulR, map_inv₀, hconjd]
      field_simp
    rw [e]
    exact hdI.mul (hd g _ _ hx hy)

  obtain ⟨m', hm'0, hm'⟩ := exists_int_isIntegral_coords b (isUnit_det_gram h v) g
  set c : F := (m' : F) * (d : F)⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hm'0) (inv_ne_zero hdF)
  have hcoordL : ∀ x ∈ dictLattice b h v d g, ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k) := by
    intro x hx i k
    have hx' : coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g := hx
    have := hm' _ (coreLattice_le_adelicLattice b g hx') (i, k)
    rw [vecCoords_coordEquiv, repr_repr_smul_inv_int] at this
    rw [hcdef, mul_assoc]
    exact this
  have hLQ : (dictLattice b h v d g).toIntSubmodule ≤ LinearMap.range (coordSpan b v c) :=
    fun x hx => mem_range_coordSpan b v hc (hcoordL x hx)

  set M : ℤ := m * d * d with hMdef
  have hM0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero hm0 hd0) hd0)
  have hLP : dictLattice b h v d g ≤ dualLattice h (dictLattice b h v d g) := fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy)
  have hnL : ∀ y ∈ dualLattice h (dictLattice b h v d g), M.natAbs • y ∈ dictLattice b h v d g := by
    intro y hy
    have h1 : (m : F) • coordEquiv F v ((d : E) • y) ∈ coreLattice b (gram h.toSesq v) g := by
      refine hm g _ fun X hX => ?_
      set x0 := (coordEquiv F v).symm X
      have hx0 : (d : E) • x0 ∈ dictLattice b h v d g := by
        rw [mem_dictLattice, inv_smul_smul₀ hdE, AddEquiv.apply_symm_apply]
        exact hX
      have h2 := (mem_integralClosure_iff ℤ E).1 (hy _ hx0)
      rw [show X = coordEquiv F v x0 from (AddEquiv.apply_symm_apply _ X).symm, pairE_coordEquiv,
        hsmulL, hconjd, ← hsmulR]
      exact h2
    have hMy : M • y ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e : (d : E)⁻¹ • (M • y) = m • ((d : E) • y) := by
        rw [← Int.cast_smul_eq_zsmul E M, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul, hMdef]
        congr 1
        push_cast
        field_simp
      rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul F]
      exact h1
    have : (M.natAbs : ℤ) • y ∈ dictLattice b h v d g := by
      rcases Int.natAbs_eq M with hM | hM
      · rwa [← hM]
      · rw [show (M.natAbs : ℤ) = -M by omega, neg_smul]
        exact neg_mem hMy
    rwa [natCast_zsmul] at this
  have hcn : c * (M.natAbs : F) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hM0)
  have hPQ : (dualLattice h (dictLattice b h v d g)).toIntSubmodule ≤ LinearMap.range (coordSpan b v (c * M.natAbs)) := by
    intro y hy
    refine mem_range_coordSpan b v hcn fun i k => ?_
    have := hcoordL _ (hnL y hy) i k
    rw [repr_repr_nsmul] at this
    rw [mul_assoc]
    exact this
  obtain ⟨hne, hle⟩ := relIndex_ne_zero_and_le_of_nsmul_mem hLP hPQ hM0 hnL
  refine ⟨⟨fun a x hx => ?_, ?_, ?_⟩, fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy),
    hne, hle.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hM0)
      (LinearMap.finrank_range_le (coordSpan b v (c * M.natAbs))))⟩
  ·
    rw [mem_dictLattice, smul_comm, coordEquiv_smul]
    exact smul_mem_coreLattice b hx a
  ·
    haveI : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule :=
      Module.Finite.of_injective (Submodule.inclusion hLQ) (Submodule.inclusion_injective hLQ)
    have := Module.Finite.iff_fg.1 (inferInstance : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule)
    exact (Submodule.fg_iff_addSubgroup_fg _).1 this
  ·
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn0, hn⟩ := exists_int_smul_single_mem_coreLattice b g i
    have hmem : (d * n) • v i ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e1 : (d : E)⁻¹ • ((d * n) • v i) = n • v i := by
        rw [← Int.cast_smul_eq_zsmul E (d * n), ← Int.cast_smul_eq_zsmul E n, smul_smul]
        congr 1
        push_cast
        field_simp
      have e2 : coordEquiv F v (v i) = Pi.single i (1 : F ⊗[F] E) := by
        funext j
        rw [coordEquiv_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
        by_cases hij : i = j
        · subst hij
          simp [Algebra.TensorProduct.one_def]
        · rw [if_neg hij, if_neg (Ne.symm hij), TensorProduct.tmul_zero]
      rw [e1, map_zsmul, e2, ← Int.cast_smul_eq_zsmul F]
      exact hn
    have hvi : v i = ((d * n : ℤ) : E)⁻¹ • ((d * n) • v i) := by
      rw [← Int.cast_smul_eq_zsmul E (d * n), inv_smul_smul₀ (by exact_mod_cast mul_ne_zero hd0 hn0)]
    rw [SetLike.mem_coe, hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end DIntegral

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem AdelicLatticeDictionary.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    AdelicLatticeDictionary.Statement h v := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_isIntegral_pairE (Module.finBasis F E) (gram h.toSesq v)
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_coreLattice_of_dual (Module.finBasis F E)
    (isUnit_det_gram h v)
  exact ⟨coreStabilizer (Module.finBasis F E) (gram h.toSesq v), _,
    dictLattice (Module.finBasis F E) h v d,
    isCompact_coreStabilizer (Module.finBasis F E) _ (isUnit_det_gram h v),
    isOpen_coreStabilizer (Module.finBasis F E) _,
    fun g => isDIntegral_dictLattice (Module.finBasis F E) h v hd0 hd hm0 hm g,
    fun γ g => dictLattice_diagonal_mul d γ g,
    fun g g' => dictLattice_eq_iff hd0⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end
end
