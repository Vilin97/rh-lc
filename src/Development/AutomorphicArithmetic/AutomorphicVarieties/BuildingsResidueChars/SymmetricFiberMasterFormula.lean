module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberIndexFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqIndex
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSumOverFibers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberCovering

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSingle

section

@[expose] public section

open MulAction in
theorem UpperTheory.orbitalFiber_single :
    UpperTheory.V.Z.Sym.Glob.Fib.OneFib := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard
  classical
  haveI hSn : S.Normal := ⟨fun n hn g => by
    convert S.mul_mem (hcomm g n) hn using 1
    group⟩
  set C := Subgroup.comap ι (S ⊔ U') with hC
  set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf
  have hΓC : Γ₁ ≤ C := fun a ha =>
    Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))
  let j : C →* G := ι.comp C.subtype
  let φ : Γ₁ →* C := Subgroup.inclusion hΓC
  have hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U') := by
    intro g hg y hy
    obtain ⟨s, hs, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨⟨s', hs'⟩, rfl⟩ := hy
    refine ⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩
    show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')
    rw [QuotientGroup.eq]
    have he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u := by group
    rw [he]
    exact hu
  have hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y := by
    intro h y
    have hg : ι h.1 ∈ S ⊔ U' := h.2
    change f (ι h.1 • y) = f y
    by_cases hy : y ∈ orbit ↥S (x : G ⧸ U')
    · have hy' := hclos _ hg y hy
      rw [hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)
      have hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [hyy, hu, hΦr _ u.2, hΦl]
    · have hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U') := fun hm => hy (by
        have := hclos _ (inv_mem hg) _ hm
        rwa [inv_smul_smul] at this)
      rw [hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]
  have hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x' := by
    obtain ⟨T, hT⟩ := hTex
    refine ⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩
    intro y hy
    obtain ⟨⟨s, hs⟩, rfl⟩ := Set.mem_of_indicator_ne_zero hy
    obtain ⟨h, hh, t, ht, u, hu, he⟩ := hT s hs
    refine ⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩
    show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')
    rw [he, QuotientGroup.eq]
    rw [show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]
    exact inv_mem hu
  have hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C := by
    ext z
    rw [Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨a, ⟨a', rfl⟩, b, hb, rfl⟩
      exact ⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hbC : b ∈ C := by
        have hb' : b = a⁻¹ * (z : Γ) := by rw [← hab]; group
        rw [hb']
        exact C.mul_mem (C.inv_mem (hΓC ha)) z.2
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C := by
    rw [hsup]
    rfl
  have key := UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f
    inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
    (by rw [hidx]; exact hrel) hinv hfin
    (fun y _ => by
      rw [← Subgroup.comap_comap]
      exact Subgroup.relIndex_comap_ne_zero _ (hst y))
  have e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f := rfl
  have hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f := by
    letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)
    exact (UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard
      (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
  rw [← hb, e1, key, hidx]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberStabilizerFinite

section

@[expose] public section

namespace UpperTheory

theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberMasterFormula

section

@[expose] public section

open MulAction in
theorem UpperTheory.symmetric_fiber_master_formula :
    UpperTheory.V.Z.Sym.Glob.Fib.Master := by
  intro Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab
  classical
  haveI hSN : S.Normal := ⟨fun s hs g => by
    have h := S.mul_mem (hcomm g s) hs
    simpa [mul_assoc] using h⟩
  have hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype := MonoidHom.ext fun γ => hι₁ γ
  have hsub : Γ₁ ≤ S.comap ι := fun γ hγ => by
    have h := (ι₁ ⟨γ, hγ⟩).2
    rw [hι₁] at h
    exact h
  have hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite := fun g =>
    UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)

  have hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 := by
    have hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'} := by
      intro z hz
      have hz' : (z : Γ) ∈ Γ₀ := Subgroup.mem_subgroupOf.1 hz
      have h := htriv _ hz' ((1 : G) : G ⧸ U')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h
      have h' : ι z ∈ U' := by simpa using U'.inv_mem h
      simpa [hι₁] using h'
    haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype
    exact Nat.card_pos.ne'
  have hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    refine UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_
    · obtain ⟨T, hT1⟩ := hfinT 1
      refine ⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩
      have e' := congrArg (Subtype.val) e
      simpa [hι₁] using e'
    · have h := hstab ((1 : G) : G ⧸ U')
      rwa [MulAction.stabilizer_quotient] at h
  have hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) /
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
    have h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
    have h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    exact div_pos (mul_pos h1 h2) h3
  intro I _ x Ux Φ hij hcov hUx hΦl hΦr
  rw [UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcover := UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx
    (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T, fun s => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 s
      exact ⟨h, t, ht, u, (hUx i u).2 hu, e⟩)
    hfinU'
  have hone := UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩
      have e' : s = ι h * t * u := by
        have e2 := congrArg (Subtype.val) e
        simpa [hι₁] using e2
      rw [e']
      group)
    hstab hd hn
  rw [hcover, hcomp]
  have hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U'
      ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hone
  rw [hC]
  push_cast
  ring
end
end
