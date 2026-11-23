module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.ContinuousEF
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PowCardEqZero
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PowCardEqZero
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FinrankImg

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiD

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
include B in
theorem d_pos : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    have := B.recon 1
    simp at this
  · exact h

def img (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin (n * d)) (Fin (n * d)) k) where
  carrier := φ B '' (S : Set (Matrix (Fin n) (Fin n) k))
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro l _ ⟨a, ha, rfl⟩
    refine ⟨(l ^ p ^ c) • a, S.smul_mem _ ha, ?_⟩
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

def coefF {m : ℕ} (w : Fin m × Fin d → k) : Fin m → k := fun l => ∑ j, w (l, j) ^ p ^ c * B.β j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem coefF_add {m : ℕ} (w w' : Fin m × Fin d → k) : coefF B (w + w') = coefF B w + coefF B w' := by
  funext l; simp only [coefF, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_smul {m : ℕ} (l : k) (w : Fin m × Fin d → k) : coefF B (l • w) = (l ^ p ^ c) • coefF B w := by
  funext l
  simp only [coefF, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum, mul_assoc]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_cF {m : ℕ} (x : Fin m → k) : coefF B (fun lj => B.cF (x lj.1) lj.2) = x := by
  funext l; exact B.recon (x l)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_inj {m : ℕ} {w w' : Fin m × Fin d → k} (h : coefF B w = coefF B w') : w = w' := by
  funext x
  obtain ⟨l, j⟩ := x
  have h1 : (fun j => w (l, j)) = fun j => w' (l, j) := by
    rw [← B.uniq (fun j => w (l, j)), ← B.uniq (fun j => w' (l, j))]
    exact congrArg B.cF (congrFun h l)
  exact congrFun h1 j

def Lmap (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    (Fin (Module.finrank k S) × Fin d → k) →ₗ[k] img B S where
  toFun w := ⟨φ B ((Module.finBasis k S).equivFun.symm (coefF B w) : Matrix (Fin n) (Fin n) k),
    ⟨_, ((Module.finBasis k S).equivFun.symm (coefF B w)).2, rfl⟩⟩
  map_add' w w' := by
    apply Subtype.ext
    simp only [coefF_add, map_add (f := _), Submodule.coe_add]
  map_smul' l w := by
    apply Subtype.ext
    simp only [coefF_smul, map_smul, SetLike.val_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem Lmap_bij (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Function.Bijective (Lmap B S) := by
  constructor
  · intro w w' h
    have h1 := φ_inj B (congrArg Subtype.val h)
    exact coefF_inj B ((Module.finBasis k S).equivFun.symm.injective (Subtype.ext h1))
  · rintro ⟨_, ⟨s, hs, rfl⟩⟩
    refine ⟨fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2, Subtype.ext ?_⟩
    have e1 : (Module.finBasis k S).equivFun.symm (coefF B fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2)
        = ⟨s, hs⟩ := by
      rw [coefF_cF, LinearEquiv.symm_apply_apply]
    exact congrArg (fun t : S => φ B (t : Matrix (Fin n) (Fin n) k)) e1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem finrank_img (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Module.finrank k (img B S) = d * Module.finrank k S := by
  have e := (LinearEquiv.ofBijective (Lmap B S) (Lmap_bij B S)).finrank_eq
  rw [← e, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

end PositivityTheory.RgUd.TP.Desc.Restr.PphiD
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PrimIdemZ

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiE

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiD

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem primIdem_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : primIdem (Z' B Z) = φ B '' primIdem Z := by
  have hinj := φ_inj B (n := n)
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  have hidem : ∀ x : Matrix (Fin n) (Fin n) k, IsIdempotentElem (φ B x) ↔ IsIdempotentElem x := fun x => by
    show φ B x * φ B x = φ B x ↔ x * x = x
    rw [← map_mul]
    exact hinj.eq_iff
  ext e'
  constructor
  · rintro ⟨he'Z, hid, hne, hmin⟩
    obtain ⟨e, heZ, rfl⟩ := (hZ e').1 he'Z
    refine ⟨e, ⟨heZ, (hidem e).1 hid, fun h => hne (by rw [h, map_zero]), fun f hfZ hf hfe => ?_⟩, rfl⟩
    rcases hmin (φ B f) ((hZ _).2 ⟨f, hfZ, rfl⟩) ((hidem f).2 hf) (by rw [← map_mul, hfe]) with h | h
    · left
      exact hinj (by rw [h, map_zero])
    · right
      exact hinj h
  · rintro ⟨e, ⟨heZ, hid, hne, hmin⟩, rfl⟩
    refine ⟨(hZ _).2 ⟨e, heZ, rfl⟩, (hidem e).2 hid, fun h => hne (hinj (by rw [h, map_zero])),
      fun f' hf'Z hf' hfe => ?_⟩
    obtain ⟨f, hfZ, rfl⟩ := (hZ f').1 hf'Z
    rcases hmin f hfZ ((hidem f).1 hf') (hinj (by rw [map_mul, hfe])) with h | h
    · left
      rw [h, map_zero]
    · right
      rw [h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem cen_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (cenSub (Z' B Z)).map (LinearMap.mulLeft k (φ B e)) = img B ((cenSub Z).map (LinearMap.mulLeft k e)) := by
  have hc : ∀ {m : ℕ} (W : Subalgebra k (Matrix (Fin m) (Fin m) k)) (x : Matrix (Fin m) (Fin m) k),
      x ∈ cenSub W ↔ x ∈ Bz W := fun W x => Iff.rfl
  have hcen := cen B Z
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    have h1 : x' ∈ φ B '' Bz Z := by
      rw [← hcen]
      exact (hc _ _).1 hx'
    obtain ⟨x, hx, rfl⟩ := h1
    exact ⟨e * x, ⟨x, (hc _ _).2 hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : φ B x ∈ Bz (Z' B Z) := by
      rw [hcen]
      exact ⟨x, (hc _ _).1 hx, rfl⟩
    exact ⟨φ B x, (hc _ _).2 h1, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem z_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (Z' B Z).toSubmodule.map (LinearMap.mulLeft k (φ B e)) = img B (Z.toSubmodule.map (LinearMap.mulLeft k e)) := by
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hZ x').1 hx'
    exact ⟨e * x, ⟨x, hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ B x, (hZ _).2 ⟨x, hx, rfl⟩, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem mu_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : mu (Z' B Z) = mu Z := by
  unfold mu
  rw [primIdem_Z', finsum_mem_image (fun x _ y _ h => φ_inj B h)]
  refine finsum_mem_congr rfl fun e _ => ?_
  rw [cen_map, z_map, finrank_img, finrank_img]
  exact Nat.mul_div_mul_left _ _ (d_pos B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiE
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PhiEx

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Restr.Pphi1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiE

theorem phiEx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k → PhiEx k := by
  intro hF p c _ _ n Z hZ hn
  obtain ⟨d, -, ⟨B⟩⟩ := fb_exists hF p c
  exact ⟨n * d, Z' B Z, φ B, e B,
    { inj := φ_inj B
      emb := φ_emb B
      econt := continuous_eF B
      econt' := continuous_eI B
      intertw := fun x v => key B x v
      carrier := coe_Z' B Z
      cen := cen B Z
      gz := gz B Z
      scal := φ_scal B
      cr := cr B Z hZ
      mu := mu_Z' B Z
      roots := roots B Z
      nil := nil B Z hn }⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Pphi1
end
end
