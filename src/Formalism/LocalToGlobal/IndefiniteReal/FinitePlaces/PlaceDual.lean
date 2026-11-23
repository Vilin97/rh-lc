module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBIv
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatIntFMat

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct



namespace Formalism.IndefR.Fin.PDB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Vi

lemma mt_mul' (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

lemma mt_one' (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

lemma splitIdem_eps {e' : AE D} (h : IsSplitIdem D e') : (e' + cA D e') * fI D = e' + cA D e' := by
  obtain ⟨-, -, v, ε, hε, hsum⟩ := h
  unfold Formalism.L2.Theta.IsPlaceIdem at hε
  obtain ⟨α, rfl, -, -⟩ := hε
  rw [hsum]
  unfold fI
  rw [← map_mul]
  congr 1
  all_goals first
    | rfl
    | (simp only [pairA]; exact Prod.ext (mul_zero _) (mul_one _))
    | (simp only [pairA]; ext <;> simp)

lemma supp_fin {e' : AE D} (he : IsSplitIdem D e') {V : HSp D} {g : GA D V} (hg : SuppAt e' V g) (i j : Fin V.rank) :
    (mt V g - 1) i j * fI D = (mt V g - 1) i j := by
  unfold SuppAt at hg
  conv_lhs => rw [← hg i j]
  rw [mul_right_comm, splitIdem_eps he, hg i j]

lemma supp_inv {e' : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e' V g) : SuppAt e' V g⁻¹ := by
  unfold SuppAt at hg ⊢
  intro i j
  have hinv : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, ← mt_mul', inv_mul_cancel, mt_one', Matrix.mul_one]
    abel
  rw [hinv, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

lemma intF_matMul {m n p : ℕ} {A : Matrix (Fin m) (Fin n) (AE D)} {B : Matrix (Fin n) (Fin p) (AE D)}
    (hA : ∀ i j, IntF (A i j)) (hB : ∀ i j, IntF (B i j)) (i : Fin m) (j : Fin p) : IntF ((A * B) i j) := by
  rw [Matrix.mul_apply]
  exact intF_sum _ _ fun k _ => intF_mul (hA i k) (hB k j)

lemma exists_nat_intF_mat {m n : ℕ} {A : Matrix (Fin m) (Fin n) (AE D)} (hA : ∀ i j, A i j * fI D = A i j) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j, IntF ((k • A) i j) := by
  choose k hk0 hk using fun (i : Fin m) (j : Fin n) => exists_nat_intF (hA i j)
  refine ⟨∏ i, ∏ j, k i j, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hk0 i j, fun i j => ?_⟩
  obtain ⟨r, hr⟩ : k i j ∣ ∏ i, ∏ j, k i j :=
    (Finset.dvd_prod_of_mem (fun j => k i j) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, k i j) (Finset.mem_univ i))
  rw [Matrix.smul_apply, hr, mul_comm (k i j) r, mul_smul]
  exact intF_nsmul (hk i j) r

lemma actO_expand {S T : HSp D} (g : GA D S) (h : GA D T) (t : WO S T) :
    actO S T g h t = t + (mt T h - 1) * t + t * (mt S g⁻¹ - 1) + (mt T h - 1) * t * (mt S g⁻¹ - 1) := by
  unfold actO
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

lemma nsmul_mul_nsmul {R : Type*} [CommRing R] {m n p : Type*} [Fintype n] (a b : ℕ) (A : Matrix m n R)
    (B : Matrix n p R) : (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma nsmul_mul_three {R : Type*} [CommRing R] {m n p q : Type*} [Fintype n] [Fintype p] (a b d : ℕ) (A : Matrix m n R)
    (B : Matrix n p R) (C : Matrix p q R) : (a • A) * (b • B) * (d • C) = (a * b * d) • (A * B * C) := by
  rw [nsmul_mul_nsmul, nsmul_mul_nsmul]


lemma four_terms {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {c c' kH kG : ℕ}
    (hlow : ∀ Z : WO S T, (∀ i j, IntF (Z i j)) → c • Z ∈ latAll S T ΛS ΛT)
    {H : Matrix (Fin T.rank) (Fin T.rank) (AE D)} {G' : Matrix (Fin S.rank) (Fin S.rank) (AE D)}
    (hH : ∀ i j, IntF ((kH • H) i j)) (hG : ∀ i j, IntF ((kG • G') i j)) {t : WO S T}
    (ht : t ∈ latAll S T ΛS ΛT) (hc't : ∀ i j, IntF ((c' • t) i j)) :
    (c * c' * kH * kG) • (t + H * t + t * G' + H * t * G') ∈ latAll S T ΛS ΛT := by
  have hZ1 : ∀ i j, IntF (((kH • H) * (c' • t)) i j) := intF_matMul hH hc't
  have hZ2 : ∀ i j, IntF (((c' • t) * (kG • G')) i j) := intF_matMul hc't hG
  have hZ3 : ∀ i j, IntF (((kH • H) * (c' • t) * (kG • G')) i j) := intF_matMul hZ1 hG
  rw [nsmul_mul_nsmul] at hZ1 hZ2
  rw [nsmul_mul_three] at hZ3
  have m1 := hlow _ hZ1
  have m2 := hlow _ hZ2
  have m3 := hlow _ hZ3
  rw [smul_smul] at m1 m2 m3
  simp only [smul_add]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · exact nsmul_mem ht _
  · have h1 := nsmul_mem m1 kG
    rw [smul_smul] at h1
    have e : c * c' * kH * kG = kG * (c * (kH * c')) := by ring
    rw [e]
    exact h1
  · have h2 := nsmul_mem m2 kH
    rw [smul_smul] at h2
    have e : c * c' * kH * kG = kH * (c * (c' * kG)) := by ring
    rw [e]
    exact h2
  · have e : c * c' * kH * kG = c * (kH * c' * kG) := by ring
    rw [e]
    exact m3

theorem placeLatDualVi (D : D7) : PlaceLatDualVi D := by
  intro ψ _ S T ΛS ΛT hS hT e' he' g h hg hh
  obtain ⟨c, hc, hlow⟩ := lower hS hT
  obtain ⟨c', hc', hup⟩ := upper hS hT
  obtain ⟨kH, hkH, hH⟩ := exists_nat_intF_mat (supp_fin he' hh)
  obtain ⟨kG, hkG, hG⟩ := exists_nat_intF_mat (supp_fin he' (supp_inv hg))
  refine ⟨c * c' * kH * kG, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hc hc') hkH) hkG, fun t ht => ?_⟩
  rw [actO_expand]
  exact four_terms hlow hH hG ht (hup t ht)

end Vi

end Formalism.IndefR.Fin.PDB

end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualASt

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT))

def PlaceLatDualIii (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT))

end Formalism.IndefR.Fin

end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct



namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

theorem splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

theorem splitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hv, by rw [cA_cA, add_comm, h3]⟩

theorem idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact ⟨Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1,
    Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (splitIdem_cA (hes PP hPP).1)⟩

theorem idemSum_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) :
    finPart D e ∈ intAE D ∧ finPart D (cA D e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine ⟨?_, ?_⟩

  · rw [map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (hes PP hPP).1

  · rw [map_sum, map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (splitIdem_cA (hes PP hPP).1)

theorem infPart_fI : infPart D (fI D) = 0 := by
  show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 0
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem half_infPart {m n : ℕ} {f : AE D} (hf : f * fI D = f) {y : Mx D m n} (hy : IsHalf f y) :
    y.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  calc infPart D (y i j) = infPart D ((f * fI D) * y i j) := by rw [hf, hy i j]
    _ = 0 := by rw [map_mul, map_mul, infPart_fI, mul_zero, zero_mul]

variable (S T : HSp D)

theorem hO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    hO S T y u = hO S T y (f • u) := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  conv_lhs => rw [← hy d a]
  ring

theorem symplO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    symplO S T y u = symplO S T y (f • u) := by
  unfold symplO; rw [hO_half_right S T hy u]

variable {S T}

theorem placeLatDualIi_of (hL : LatSelfDual D) : PlaceLatDualIi D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he y hy
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, hfc⟩ := idemSum_mul_fI he
  have hie := (idemSum_int he).1
  have hee := idemSum_mul_self he
  have hy0 : y.map (infPart D) = 0 := half_infPart hfc hy
  constructor
  · intro hx
    refine (hL4 y hy0).2 fun u hu => ?_
    have hm : e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hie hu
    have hh : IsHalf e (e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
    have h1 := hx _ hm hh
    rw [symplO_half_right S T hy u, symplO_swap S T (e • u) y, AddChar.map_neg_eq_inv, h1, inv_one]
  · intro hyL x hx hxh
    exact (hL4 x (half_infPart hfe hxh)).1 hx y hyL

theorem placeLatDualIii_of (hL : LatSelfDual D) : PlaceLatDualIii D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he x hx
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, -⟩ := idemSum_mul_fI he
  have hic := (idemSum_int he).2
  have hee := idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hx0 : x.map (infPart D) = 0 := half_infPart hfe hx
  have hxc : IsHalf (cA D (cA D e)) x := by rw [cA_cA]; exact hx
  constructor
  · intro hy
    refine (hL4 x hx0).2 fun u hu => ?_
    have hm : cA D e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hic hu
    have hh : IsHalf (cA D e) (cA D e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
    rw [symplO_half_right S T hxc u]
    exact hy _ hm hh
  · intro hxL y hy _
    exact (hL4 x hx0).1 hxL y hy

end Formalism.IndefR.Fin.PDA

end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDual

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

theorem placeLatDual_of {D : D7} (hL : LatSelfDual D) : PlaceLatDual D := by
  intro ψ hψ S T ΛS ΛT hS hT
  refine ⟨fun e' he' u hu => latO_map_splitIdem S T ΛS ΛT he' hu,
    fun e' he' g h hg hh => PDB.placeLatDualVi D ψ hψ S T ΛS ΛT hS hT e' he' g h hg hh,
    fun P e he => ⟨PDA.placeLatDualIi_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDA.placeLatDualIii_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualIv D ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualV D ψ hψ S T ΛS ΛT hS hT P e he⟩⟩

end Formalism.IndefR.Fin

end
end
end
