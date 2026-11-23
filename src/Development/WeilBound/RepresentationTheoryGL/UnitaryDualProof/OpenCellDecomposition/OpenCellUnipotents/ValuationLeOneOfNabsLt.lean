module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.ValuationOneApplyLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.OpenJ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Translate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Translate

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.JTranslate

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem J_translate (ψ : AddChar k Circle) (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ)
    (hV : ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
        (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (L₀ : Subgroup (GL (Fin N) k)) (hL₀U : L₀ ≤ unipU k d hd) (hc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hO : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀)
    (hθ : ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1)
    (F : IndSp (stdBlocks d hd) ρ) (hF : F ∈ openFns d hd ρ) (v : W)
    (hF1 : ∀ u ∈ L₀, F.1.1 (pm k (wOpen d hd) * u) = v)
    (hF0 : ∀ u ∈ unipU k d hd, u ∉ L₀ → F.1.1 (pm k (wOpen d hd) * u) = 0)
    (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    (haU : ∀ u ∈ unipU k d hd, a * u * a⁻¹ ∈ unipU k d hd)
    (haU' : ∀ u ∈ unipU k d hd, a⁻¹ * u * a ∈ unipU k d hd)
    (hstab : ∀ u ∈ L₀, a * u * a⁻¹ ∈ L₀) :
    (J ⟨F, hF⟩ = (vol L₀ : ℂ) • v) ∧
    ∃ hm : parInd (stdBlocks d hd) ρ a F ∈ openFns d hd ρ,
      J ⟨parInd (stdBlocks d hd) ρ a F, hm⟩ = (vol (L₀.map (MulAut.conj a).toMonoidHom) : ℂ) •
        ((deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v) := by
  have hcont : Continuous fun g : GL (Fin N) k => a * g * a⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem1 : ∀ x : GL (Fin N) k, x ∈ L₀.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L₀ := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : a⁻¹ * ((MulAut.conj a).toMonoidHom y) * a = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hy']
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hback : ∀ x : GL (Fin N) k, x = a * (a⁻¹ * x * a) * a⁻¹ := fun x => by group
  refine ⟨?_, PositivityTheory.RgUd.CellA.translate_mem_openFns d hd ρ a l hl haB hF, ?_⟩
  · refine (hV L₀ hL₀U hc hO).2 ⟨F, hF⟩ v ?_ hF0
    intro u hb hu
    rw [hθ u hb hu]
    simpa using hF1 u hu
  · have hL₁U : L₀.map (MulAut.conj a).toMonoidHom ≤ unipU k d hd := by
      intro x hx
      rw [hmem1] at hx
      rw [hback x]
      exact haU _ (hL₀U hx)
    have hL₁c : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) := by
      rw [Subgroup.coe_map]
      exact hc.image hcont
    have hL₁O : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        (L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) := by
      obtain ⟨O, hOo, hOeq⟩ := hO
      have hc2 : Continuous fun g : GL (Fin N) k => a⁻¹ * g * a :=
        (continuous_const.mul continuous_id).mul continuous_const
      refine ⟨(fun g : GL (Fin N) k => a⁻¹ * g * a) ⁻¹' O, hOo.preimage hc2, ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
      rw [hmem1]
      constructor
      · rintro ⟨hxO, hxU⟩
        have : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := ⟨hxO, haU' x hxU⟩
        rw [hOeq] at this
        exact this
      · intro hx
        have hx' : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
          rw [hOeq]
          exact hx
        refine ⟨hx'.1, ?_⟩
        rw [hback x]
        exact haU _ hx'.2
    refine (hV _ hL₁U hL₁c hL₁O).2 _ _ ?_ ?_
    · intro u hb hu
      have hu0 : a⁻¹ * u * a ∈ L₀ := (hmem1 u).1 hu
      have huL₀ : u ∈ L₀ := by
        rw [hback u]
        exact hstab _ hu0
      have key : ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) =
          (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v := by
        rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u, hF1 _ hu0]
      rw [hθ u hb huL₀]
      simpa using key
    · intro u hu hnot
      show ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) = 0
      rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u]
      have hn : a⁻¹ * u * a ∉ L₀ := fun h => hnot ((hmem1 u).2 h)
      rw [hF0 _ (haU' u hu) hn, map_zero, smul_zero]

end PositivityTheory.RgUd.CellA
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.MemUnipUTwo

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

variable {r m : ℕ}

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wConj_apply (u : GL (Fin (r + m)) k) (i j : Fin (r + m)) :
    ((pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ : GL (Fin (r + m)) k) :
      Matrix (Fin (r + m)) (Fin (r + m)) k) i j =
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm i) ((w2 r m).symm j) := by
  rw [wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply]
  rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_unipU_two {u : GL (Fin (r + m)) k} :
    u ∈ unipU k (dd r m) (hdd r m) ↔ u ∈ unipB k (Fin (r + m)) ∧ ∀ i j : Fin (r + m),
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j →
        (i : ℕ) < m ∧ m ≤ (j : ℕ) := by
  set e := stdBlocks (dd r m) (hdd r m) with he
  have hblk : ∀ (a : Fin 2) (i' : Fin (dd r m a)), ((w2 r m).symm (e ⟨a, i'⟩) : ℕ) < m ↔ a = 1 := by
    intro a i'
    have := weyl_shuffle_symm_lt_iff (r := r) (m := m) (e ⟨a, i'⟩)
    rwa [blk_apply] at this
  have hone : ∀ (a b : Fin 2) (i' : Fin (dd r m a)) (j' : Fin (dd r m b)),
      (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨b, j'⟩)) =
        if (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩ then 1 else 0 := by
    intro a b i' j'
    rw [Matrix.one_apply]
    by_cases h : (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (e.injective ((w2 r m).symm.injective h')))]
  constructor
  · intro hu
    refine ⟨hu.1, fun p q hpq => ?_⟩
    have h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈
        unipRadLower k e := hu.2
    obtain ⟨hP, hD⟩ := (mem_unipRadLower k).1 h2
    obtain ⟨⟨a, i'⟩, hi⟩ := e.surjective (w2 r m p)
    obtain ⟨⟨b, j'⟩, hj⟩ := e.surjective (w2 r m q)
    have hp : p = (w2 r m).symm (e ⟨a, i'⟩) := by rw [hi, Equiv.symm_apply_apply]
    have hq : q = (w2 r m).symm (e ⟨b, j'⟩) := by rw [hj, Equiv.symm_apply_apply]
    have hpa := hblk a i'
    have hqb := hblk b j'
    rw [← hp] at hpa
    rw [← hq] at hqb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exfalso
      have h3 := (mem_parabLower_iff k).1 hP a b i' j' hab
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
    · exfalso
      have h3 := hD a i' j'
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, Matrix.one_apply]
      by_cases h : i' = j'
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (by simpa using h'))]
    · have ha : a = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      refine ⟨hpa.2 ha, ?_⟩
      by_contra hq'
      push_neg at hq'
      exact absurd (hqb.1 hq') (by rw [hb]; decide)
  · rintro ⟨hB, hc⟩
    refine ⟨hB, ?_⟩
    show pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e
    refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i' j' hab => ?_, fun a i' j' => ?_⟩
    · rw [wConj_apply]
      have ha : a = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      by_contra hne
      have h1 := hc _ _ (by
        rw [hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
        exact hne)
      have h2 := (hblk a i').1 h1.1
      rw [ha] at h2
      exact absurd h2 (by decide)
    · rw [wConj_apply]
      have hpq : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨a, j'⟩)) =
          (1 : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i' j' := by
        rw [hone, Matrix.one_apply]
        by_cases h' : i' = j'
        · subst h'
          simp
        · rw [if_neg (fun h => h' (by simpa using h)), if_neg h']
      rw [← hpq]
      by_contra hne
      obtain ⟨h1, h2⟩ := hc _ _ hne
      exact absurd ((hblk a j').2 ((hblk a i').1 h1)) (not_lt.2 h2)

end PositivityTheory.RgUd.CellA
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.ValuationLeOneOfNabsLt

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker
open GroundTheory.Automorphic.GLnLocal ValuativeRel

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_one_of_nabs_lt (z : kˣ) (hz : nabs k z < 1) : valuation k (z : k) ≤ 1 := by
  have h := (nabs_le_iff z 1).1 (by rw [nabs_one]; exact hz.le)
  simpa using h

theorem scalar_id (t : ℝ) (ht : 0 < t) (i m r : ℕ) :
    (t ^ i) ^ (m * r) * (t ^ i) ^ (-((m * r : ℕ) : ℝ) / 2) = Real.sqrt t ^ (i * m * r) := by
  have hti : 0 < t ^ i := pow_pos ht i
  rw [← Real.rpow_natCast (t ^ i) (m * r), ← Real.rpow_add hti, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)), ← Real.rpow_mul ht.le, ← Real.rpow_natCast t i,
    ← Real.rpow_mul ht.le]
  congr 1
  push_cast
  ring

variable {r m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]



theorem openCellPar (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (ρ : Representation ℂ (Levi k fun a => Fin (dd r m a)) W) (hρ : IsSmooth ρ) (ω : kˣ →* ℂˣ)
    (hcent : ∀ (z : kˣ) (t : W), ρ (levZ k r m z) t = (ω z : ℂ) • t)
    (hv : ∃ v, v ∉ twKer ρ (unipM k (dd r m)) (whitM (dd r m) ψ)) (z : kˣ) (hz : nabs k z < 1) :
    ∃ F : IndSp (stdBlocks (dd r m) (hdd r m)) ρ,
      F ∉ twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) ∧
      ∀ i : ℕ, parInd (stdBlocks (dd r m) (hdd r m)) ρ (aDiag k (r + m) m (z ^ i)) F -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • F ∈
          twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) := by
  obtain ⟨v, hv⟩ := hv
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  have hJ := CellB.openJ k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ
  rcases hJ with ⟨J, vol, -, hJker, hJU, -, hJvol⟩
  have hbump := exists_bump k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ v
  rcases hbump with ⟨n, -, hwhit, hcpt, hopen, f, hf, hfv, hf0⟩
  have hle : CellB.congrL k r m n ≤ unipU k (dd r m) (hdd r m) := inf_le_left
  have hwL : ∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))),
      u ∈ CellB.congrL k r m n → whitChar ψ (r + m) ⟨u, hb⟩ = 1 :=
    fun u hb hu => hwhit u hb (CellB.mem_congrL.1 hu).2
  obtain ⟨hpos, hJf⟩ := hJvol _ hle hcpt hopen
  have hJ0 := hJf ⟨f, hf⟩ v (fun u hb hu => by
    rw [hwL u hb hu, Units.val_one, one_smul]; exact hfv u hu) hf0
  have hz1 := valuation_le_one_of_nabs_lt z hz
  refine ⟨f, ?_, fun i => ?_⟩
  · intro h
    have h2 := (hJker ⟨f, hf⟩).2 h
    rw [hJ0] at h2
    exact hv ((Submodule.smul_mem_iff _ (Complex.ofReal_ne_zero.2 hpos.ne')).1 h2)
  · have hval : valuation k ((z ^ i : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one₀ zero_le' hz1
    set a := aDiag k (r + m) m (z ^ i) with ha
    have hconj := conj_aDiag (r := r) (m := m) k (z ^ i)
    have hB : ∀ u ∈ unipB k (Fin (r + m)), a * u * a⁻¹ ∈ unipB k (Fin (r + m)) :=
      fun u hu => aDiag_conj_mem_unipB k _ m (z ^ i) hu
    have hU : ∀ u ∈ unipU k (dd r m) (hdd r m), a * u * a⁻¹ ∈ unipU k (dd r m) (hdd r m) :=
      fun u hu => aDiag_conj_mem_unipU k (z ^ i) hu
    have hUi : ∀ u ∈ unipU k (dd r m) (hdd r m), a⁻¹ * u * a ∈ unipU k (dd r m) (hdd r m) := by
      intro u hu
      have h := aDiag_conj_mem_unipU (r := r) (m := m) k (z ^ i)⁻¹ hu
      rwa [← aDiag_inv, inv_inv] at h
    have hLc : ∀ u ∈ CellB.congrL k r m n, a * u * a⁻¹ ∈ CellB.congrL k r m n := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := CellB.mem_congrL.1 hu
      exact CellB.mem_congrL.2 ⟨hU u hu1,
        aDiag_conj_mem_congr k _ m (z ^ i) hval n ((mem_unipU_two k).1 hu1).1 hu2⟩
    obtain ⟨_, hm, hJa⟩ := J_translate ψ J vol hJvol _ hle hcpt hopen hwL f hf v hfv hf0
      a (levZ k r m (z ^ i)) hconj hB hU hUi hLc
    set δ : ℂ := ((deltaHalf k (fun a : Fin 2 => Fin (dd r m a)) (levZ k r m (z ^ i)) : ℂˣ) : ℂ)
      with hδ
    have hvol := CellB.vol_conj_aDiag ψ ρ J vol hJU hJvol (fun u => mem_unipU_two k) n (z ^ i) hval
      hwL ⟨_, hm⟩ (δ • ρ (levZ k r m (z ^ i)) v)
      (by rw [hcent]; exact smul_ne_zero (Units.ne_zero _) (smul_ne_zero (Units.ne_zero _) hv0))
      (fun u hu => by
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show a⁻¹ * (a * u' * a⁻¹) * a = u' by group, hfv u' hu'])
      (fun u hu hnu => by
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        rw [hf0 _ (hUi u hu) (fun h => hnu (Subgroup.mem_map.2 ⟨a⁻¹ * u * a, h, by
          show a * (a⁻¹ * u * a) * a⁻¹ = u
          group⟩)), map_zero, smul_zero])
    have hmem : parInd (stdBlocks (dd r m) (hdd r m)) ρ a f -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • f ∈
          openFns (dd r m) (hdd r m) ρ := sub_mem hm (Submodule.smul_mem _ _ hf)
    apply (hJker ⟨_, hmem⟩).1
    have hsplit : J ⟨_, hmem⟩ = J ⟨_, hm⟩ -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • J ⟨f, hf⟩ := by
      rw [← map_smul, ← map_sub]
      rfl
    rw [hsplit, hJa, hJ0, hvol, hcent, hδ, deltaHalf_levZ, nabs_pow]
    convert Submodule.zero_mem _
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
    convert zero_smul ℂ v
    rw [sub_eq_zero, map_pow, Units.val_pow_eq_pow_val, ← Complex.ofReal_pow,
      ← scalar_id (nabs k z) (GlobalTheory.SplitWeil.nabs_pos k z) i m r]
    push_cast
    ring

end PositivityTheory.RgUd.CellA
end
end
end
