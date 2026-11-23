module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Mathlib.Algebra.Module.Lattice.Full
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj
import Mathlib.RingTheory.Ideal.Quotient.Index
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeProperties.LeftMulMatrixEmbeddingDetEqNorm

section

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.GL

section Mat

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]

variable (O) in
def Ent (g : GL (Fin 2) K) : Prop := ∀ s t, (g : Matrix (Fin 2) (Fin 2) K) s t ∈ Set.range (algebraMap O K)

abbrev sc (s : Kˣ) : GL (Fin 2) K := GeneralLinearGroup.scalar (Fin 2) s

theorem sc_val (s : Kˣ) : ((sc s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (s : K) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [sc, GeneralLinearGroup.scalar, h]

theorem sc_comm (s : Kˣ) (g : GL (Fin 2) K) : sc s * g = g * sc s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_val, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem kg_ent {g : GL (Fin 2) K} (h : g ∈ KG O K) : Ent O g := by
  obtain ⟨a, rfl⟩ := h
  exact fun s t => ⟨(a : Matrix (Fin 2) (Fin 2) O) s t, rfl⟩

theorem kg_det {g : GL (Fin 2) K} (h : g ∈ KG O K) :
    ∃ u : Oˣ, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨GeneralLinearGroup.det a, ?_⟩
  simp [RingHom.map_det]

theorem kg_of_det [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) : g ∈ KG O K := by
  choose a ha using h
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = (algebraMap O K).mapMatrix (Matrix.of a) := by
    ext s t
    simp [ha]
  have hd : (Matrix.of a).det = u := by
    apply IsFractionRing.injective O K
    rw [RingHom.map_det, ← hg, hu]
  refine ⟨GeneralLinearGroup.mk'' (Matrix.of a) (hd ▸ u.isUnit), Units.ext ?_⟩
  rw [hg]
  rfl

theorem ent_det {g : GL (Fin 2) K} (h : Ent O g) : ∃ r : O, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K r := by
  choose a ha using h
  exact ⟨a 0 0 * a 1 1 - a 0 1 * a 1 0, by simp [det_fin_two, ha]⟩

theorem kg_of_inv [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (h' : Ent O g⁻¹) : g ∈ KG O K := by
  obtain ⟨r, hr⟩ := ent_det h
  obtain ⟨r', hr'⟩ := ent_det h'
  have : r * r' = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, ← hr, ← hr', ← det_mul, ← Units.val_mul, mul_inv_cancel, map_one]
    simp
  exact kg_of_det h (Units.mkOfMulEqOne r r' this) hr

theorem zk_iff {g : GL (Fin 2) K} : g ∈ ZK O K ↔ ∃ s : Kˣ, ∃ k ∈ KG O K, g = sc s * k := by
  constructor
  · intro h
    haveI : (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.Normal := ⟨by
      rintro _ ⟨s, rfl⟩ g
      exact ⟨s, by rw [← sc_comm s g, mul_inv_cancel_right]⟩⟩
    have h' : g ∈ ((ZK O K : Subgroup _) : Set (GL (Fin 2) K)) := h
    rw [ZK, Subgroup.normal_mul] at h'
    obtain ⟨_, ⟨s, rfl⟩, k, hk, rfl⟩ := h'
    exact ⟨s, k, hk, rfl⟩
  · rintro ⟨s, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup ⟨s, rfl⟩ hk

theorem ent_of_zk [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {g : GL (Fin 2) K} (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) (h : g ∈ ZK O K) : Ent O g := by
  obtain ⟨w, k, hk, rfl⟩ := zk_iff.1 h
  obtain ⟨v, hv⟩ := kg_det hk
  have hw : ∃ r : O, algebraMap O K r = w := by
    rcases ValuationRing.isInteger_or_isInteger O (w : K) with h | ⟨r, hr⟩
    · exact h
    · rw [Units.val_mul, sc_val, det_mul, det_smul, hv] at hu
      have : r * (r * u) = v := by
        apply IsFractionRing.injective O K
        rw [map_mul, map_mul, hr, ← hu]
        simp
        field_simp
      have hr' : IsUnit r := isUnit_of_mul_isUnit_left (this ▸ v.isUnit)
      obtain ⟨r', hr''⟩ := hr'.exists_right_inv
      refine ⟨r', ?_⟩
      have := congrArg (algebraMap O K) hr''
      rw [map_mul, hr, map_one] at this
      field_simp at this
      exact this
  obtain ⟨r, hr⟩ := hw
  intro s t
  obtain ⟨a, ha⟩ := kg_ent hk s t
  exact ⟨r * a, by simp [sc_val, hr, ha]⟩

end Mat

section LL

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

variable (τ) in
abbrev b0 : Module.Basis (Fin 2) K (Etau K τ) := QuadraticAlgebra.basis (-1) τ

variable (τ) in
abbrev j0 : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (b0 τ)

theorem leftMulMatrixEmbedding_omega_trace : (j0 τ ω).trace = τ := by
  simp [Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

theorem leftMulMatrixEmbedding_det_eq_norm (x : Etau K τ) : (j0 τ x).det = QuadraticAlgebra.norm x := by
  simp [Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis, QuadraticAlgebra.norm_def]
  ring

variable (τ) in
def su (s : Kˣ) : (Etau K τ)ˣ := Units.map (algebraMap K (Etau K τ) : K →* Etau K τ) s

theorem su_mul (s : Kˣ) (x : Etau K τ) : (su τ s : Etau K τ) * x = (s : K) • x := by
  simp [su, Algebra.smul_def]

theorem jU_su (s : Kˣ) : jU (j0 τ) (su τ s) = sc s := by
  apply Units.ext
  rw [sc_val]
  change j0 τ (algebraMap K _ (s : K)) = _
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

variable (O τ) in
def LL (g : GL (Fin 2) K) : Set (Etau K τ) :=
  {x | ∀ i, (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) i ∈ Set.range (algebraMap O K)}

theorem lat_mul (t : (Etau K τ)ˣ) (g : GL (Fin 2) K) :
    LL O τ (jU (j0 τ) t * g) = ((t : Etau K τ) * ·) '' LL O τ g := by
  have h : ∀ x, x ∈ LL O τ (jU (j0 τ) t * g) ↔ ((t⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x ∈ LL O τ g := by
    intro x
    simp only [LL, Set.mem_setOf_eq]
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, ← mulVec_mulVec, ← Algebra.leftMulMatrix_mulVec_repr]
    rfl
  ext x
  rw [h]
  constructor
  · exact fun hx => ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem lat_sc (s : Kˣ) (g : GL (Fin 2) K) : LL O τ (sc s * g) = ((s : K) • ·) '' LL O τ g := by
  rw [← jU_su (τ := τ), lat_mul]
  simp only [su_mul]

theorem lat_le {g g' : GL (Fin 2) K} : LL O τ g ⊆ LL O τ g' ↔ Ent O (g'⁻¹ * g) := by
  constructor
  · intro h s t
    have := h (a := (b0 τ).equivFun.symm ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single t 1)) (by
      intro i
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mulVec]
      by_cases h : i = t
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩) s
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul] at this
    simpa using this
  · intro h x hx i
    have e : ((g'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x =
        ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]
    rw [e]
    choose a ha using h
    choose v hv using hx
    refine ⟨a i 0 * v 0 + a i 1 * v 1, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ha, ha, hv, hv]
    generalize ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = w
    simp [mulVec, dotProduct]

theorem lat_basis [IsDomain O] [IsFractionRing O K] (B : Module.Basis (Fin 2) K (Etau K τ)) (g : GL (Fin 2) K)
    (h : ∀ x, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = B.repr x) :
    LL O τ g = Submodule.span O (Set.range B) := by
  ext x
  rw [SetLike.mem_coe, B.mem_span_iff_repr_mem O, ← h]
  rfl

theorem lat_isLat [IsDomain O] [IsFractionRing O K] (g : GL (Fin 2) K) : IsLat O τ (LL O τ g) := by
  classical
  let B : Module.Basis (Fin 2) K (Etau K τ) :=
    Module.Basis.ofEquivFun ((b0 τ).equivFun ≪≫ₗ (GeneralLinearGroup.toLin g⁻¹).toLinearEquiv)
  have h := lat_basis (O := O) B g fun x => rfl
  refine ⟨⟨Finset.univ.image B, by rw [h]; simp⟩, ?_⟩
  rw [h, Submodule.span_span_of_tower, B.span_eq]

theorem isLat_lat [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {S : Set (Etau K τ)}
    (hS : IsLat O τ S) : ∃ g, S = LL O τ g := by
  obtain ⟨⟨s, rfl⟩, hsp⟩ := hS
  set M : Submodule O (Etau K τ) := Submodule.span O (s : Set (Etau K τ)) with hM
  haveI : Submodule.IsLattice K M := Submodule.IsLattice.of_fg K ⟨s, rfl⟩
  haveI : Submodule.IsFullLattice K M := ⟨hsp⟩
  have hr : Module.finrank O M = 2 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsFullLattice.rank_eq K M, ← Module.finrank_eq_rank, QuadraticAlgebra.finrank_eq_two]
  let b := Module.finBasisOfFinrankEq O M hr
  let B := b.extendOfIsFullLattice K
  refine ⟨⟨(b0 τ).toMatrix B, B.toMatrix (b0 τ), by simp, by simp⟩, ?_⟩
  rw [lat_basis B _ fun x => (b0 τ).toMatrix_mulVec_repr B x]
  have : Set.range B = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [B]
  rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem cls_self (S : Set (Etau K τ)) : S ∈ cls τ S := ⟨1, by simp⟩

theorem cls_smul (s : Kˣ) (S : Set (Etau K τ)) : cls τ (((s : K) • ·) '' S) = cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r * s, by simp [← Set.image_comp, Function.comp_def, mul_smul]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r * s⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩

theorem cls_lat [IsFractionRing O K] {g g' : GL (Fin 2) K} :
    cls τ (LL O τ g) = cls τ (LL O τ g') ↔ g⁻¹ * g' ∈ ZK O K := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ : LL O τ g' ∈ cls τ (LL O τ g) := h ▸ cls_self _
    rw [← lat_sc] at hs
    refine zk_iff.2 ⟨s, (sc s * g)⁻¹ * g', kg_of_inv (lat_le.1 hs.subset) ?_, ?_⟩
    · have := lat_le.1 hs.superset
      rwa [_root_.mul_inv_rev, inv_inv]
    · rw [← mul_assoc, sc_comm s (sc s * g)⁻¹]
      group
  · intro h
    obtain ⟨s, k, hk, e⟩ := zk_iff.1 h
    have e' : (sc s * g)⁻¹ * g' = k := by
      rw [sc_comm, _root_.mul_inv_rev, mul_assoc, e, inv_mul_cancel_left]
    have : LL O τ g' = LL O τ (sc s * g) := by
      refine Set.Subset.antisymm (lat_le.2 (e' ▸ kg_ent hk)) (lat_le.2 ?_)
      have := kg_ent ((KG O K).inv_mem hk)
      rwa [← e', _root_.mul_inv_rev, inv_inv] at this
    rw [this, lat_sc, cls_smul]

end LL

end UpperTheory.V.Z.Sym.Loc.GL
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinBetween

section

@[expose] public section

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem fin_between {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
    (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (x : Etau K τ) (hx : x.im ≠ 0) :
    {S : Set (Etau K τ) | IsLat O τ S ∧ 1 ∈ S ∧ x ∈ S ∧ ∀ w ∈ S, IsIntegral O w}.Finite := by
  haveI := L.frac
  classical
  obtain ⟨N, hN, hden⟩ := int_denom L hτ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) ({-x.re / x.im, 1 / x.im} : Finset K)
  obtain ⟨p, hp⟩ := hr _ (Finset.mem_insert_self _ _)
  obtain ⟨q, hq⟩ := hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [Algebra.smul_def] at hp hq
  haveI := finite_quot_span L (mul_ne_zero hN (nonZeroDivisors.coe_ne_zero r))
  let M := integralClosure O (Etau K τ)
  haveI : Module.Finite O M := Module.Finite.iff_fg (N := Subalgebra.toSubmodule M).2 (intE_fg L hτ)
  let I : Submodule O M := Ideal.span {N * r} • ⊤
  haveI : Finite (M ⧸ I) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let f : Set (M ⧸ I) → Set (Etau K τ) := fun A => Subtype.val '' (I.mkQ ⁻¹' A)
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨⟨⟨g, rfl⟩, -⟩, h1, h2, h3⟩
  set T := Submodule.span O (g : Set (Etau K τ))
  refine ⟨I.mkQ '' (Subtype.val ⁻¹' (T : Set (Etau K τ))), ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
    have h4 : y - z ∈ (Ideal.span {N * r} • ⊤ : Submodule O M) := (Submodule.Quotient.eq _).1 e.symm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨m, -, hm⟩ := h4
    have hm' : (N * r) • (m : Etau K τ) = y - z := congrArg Subtype.val hm
    obtain ⟨a, b, ha, hb⟩ := hden _ m.2
    have e2 : (y : Etau K τ) = z + ((r * a + b * p) • (1 : Etau K τ) + (b * q) • x) := by
      rw [← sub_eq_iff_eq_add', ← hm', ← algebraMap_smul K (N * r), ← algebraMap_smul K (r * a + b * p), ← algebraMap_smul K (b * q)]
      simp only [map_mul, map_add (f := _), hp, hq, ← ha, ← hb]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, - algebraMap_smul] <;> field_simp <;> ring
    rw [e2]
    exact T.add_mem hz (T.add_mem (T.smul_mem _ h1) (T.smul_mem _ h2))
  · intro hw
    exact ⟨⟨w, h3 w hw⟩, ⟨⟨w, h3 w hw⟩, hw, rfl⟩, rfl⟩

open UpperTheory.V.Z.Sym.Loc.GL in
theorem UpperTheory.V.Z.Sym.Loc.finG : UpperTheory.V.Z.Sym.Loc.FinG := by
  intro O K _ _ _ _ _ Δ τ L hτ j hj z hz
  haveI := L.frac
  classical
  obtain ⟨g, hg⟩ := (gConj O K Δ τ L hτ (j0 τ) j leftMulMatrixEmbedding_omega_trace hj).1
  have det : ∀ (y : GL (Fin 2) K) (s : Kˣ) (k : GL (Fin 2) K), k ∈ KG O K → y⁻¹ * jU j z * y = sc s * k →
      ∃ e : Oˣ, QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K e * (s : K) ^ 2 := fun y s k hk e => by
    obtain ⟨u, hu⟩ := kg_det hk
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
    simp only [Units.val_mul] at this
    rw [Matrix.det_units_conj', Matrix.det_mul, hu, sc_val, Matrix.det_smul] at this
    exact ⟨u, by rw [← j_det j hj]; exact this.trans (by simp [mul_comm])⟩
  by_cases h0 : ∃ y₀ : GL (Fin 2) K, y₀⁻¹ * jU j z * y₀ ∈ ZK O K
  swap
  · exact ⟨∅, fun y hy => absurd ⟨y, hy⟩ h0⟩
  obtain ⟨y₀, hy₀⟩ := h0
  obtain ⟨s, k₀, hk₀, e₀⟩ := zk_iff.1 hy₀
  obtain ⟨ε, hε⟩ := det y₀ s k₀ hk₀ e₀
  let u : (Etau K τ)ˣ := su τ s⁻¹ * z
  have hun : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, Algebra.smul_def, map_mul, QuadraticAlgebra.norm_algebraMap, hε, Units.val_inv_eq_inv_val]
    field_simp
  have hui : (u : Etau K τ).im ≠ 0 := by
    rw [Units.val_mul, su_mul]
    simpa using hz
  have fin := fin_between L hτ u hui
  choose! rep hrep using fun S (h : IsLat O τ S) => isLat_lat h
  refine ⟨fin.toFinset.image fun S => g⁻¹ * rep S, fun y hy => ?_⟩
  have h1 : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) ∈ ZK O K := by
    have : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) = sc s⁻¹ * (y⁻¹ * jU j z * y) := by
      rw [map_mul, jU_su, hg, mul_assoc (sc s⁻¹), ← mul_assoc, ← sc_comm]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) hy
  have h2 := ent_of_zk ε (by
    rw [← mul_assoc, Units.val_mul, Units.val_mul, Matrix.det_units_conj', ← hun]; exact leftMulMatrixEmbedding_det_eq_norm _) h1
  have h3 := lat_le (τ := τ).2 h2
  rw [lat_mul] at h3
  obtain ⟨t, ht⟩ := PS.gen_ex L hτ (lat_isLat (O := O) (g * y))
  have hl := PS.lat_ml (lat_isLat (O := O) (τ := τ) (g * y)) t⁻¹
  have hm : PS.ml t⁻¹ (LL O τ (g * y)) ∈ fin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨hl, PS.mem_ml.2 (by simpa using ht.1), PS.mem_ml.2 ?_, ?_⟩
    · rw [inv_inv, mul_comm]; exact h3 ⟨_, ht.1, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ht.2 w hw
  refine ⟨t, _, Finset.mem_image_of_mem _ hm, (jU j t * (g⁻¹ * rep (PS.ml t⁻¹ (LL O τ (g * y)))))⁻¹ * y, ?_, by group⟩
  have : cls τ (LL O τ (jU (j0 τ) t * rep (PS.ml t⁻¹ (LL O τ (g * y))))) = cls τ (LL O τ (g * y)) := by
    rw [lat_mul, ← hrep _ hl]
    change cls τ (PS.ml _ _) = _
    rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  rw [cls_lat] at this
  rw [hg]
  simpa [mul_assoc] using this
end
end
