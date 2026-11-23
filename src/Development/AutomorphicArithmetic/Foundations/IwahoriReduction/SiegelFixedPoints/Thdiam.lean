module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
public import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
public import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocitStatement
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Actcls
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.ExistsSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Imports

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.Kd.L.twist :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), Odd w → ∃ (c₁ : ℕ) (κ : ℚ), κ ≠ 0 ∧ ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ (y : (ZMod (l ^ m))ˣ) (δ : (ZMod N)ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ s, Stab A s → (∀ a ∈ A, A.valuation (s a - a) < 1) → s (zt ε l m) = zt ε l m → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y)) φ → ∀ tt : ZMod (l ^ n), IsLamG ε l n m s tt → ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ i : ℕ, CgA A l n ((l : Ω) ^ c₁ * φ.coeff (i : ℚ)) ((l : Ω) ^ c₁ * ((l : Ω) ^ c₀ * (κ : Ω) * (tt.val : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) + (s (g.coeff (i : ℚ)) - g.coeff (i : ℚ))) := by
  intro l _ N _ w hw
  obtain ⟨c₁, κ, hκ, H⟩ := UpperTheory.Kd.L.law l N w hw
  refine ⟨c₁, κ, hκ, ?_⟩
  intro Ω _ _ _ _ ε X c d gm hP hG1 A hA x m n c₀ hm hmn bB hB y δ
  have hl : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hl.ne_zero
  have hcopδ : ((δ : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime δ
  have hD : IsDiam N l (δ : ZMod N).val (sgD N l (δ : ZMod N).val) :=
    DiamU.isDiam_sgD_of_coprime' hl0 hcopδ
  obtain ⟨hP', hL⟩ := actcls ε X l N c d gm hP _ hD.1
  obtain ⟨g, hgA, hg⟩ := H ε X c d (fun r => gm r * sgD N l (δ : ZMod N).val) hP' A hA x m n c₀ hm hmn
    (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))
    (fun σ hσ => hL x w m n c₀ hw hm σ (bB σ) (hB σ hσ)) y
  refine ⟨g, hgA, ?_⟩
  intro s hs1 hs2 hs3 φ hφ tt htt β t hβy hβ1 hlt i
  have key := hg s hs1 hs2 hs3 φ ?_ tt htt β t (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) ?_ hβy hβ1 hlt i
  · rw [show ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ))
        = (x.val : ℤ) * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring,
      show t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) = (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring]
    exact key
  · have hNM : NeZero (topM l n m (N * N)) :=
      ⟨by unfold topM; exact mul_ne_zero (pow_ne_zero _ hl0) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hcop : N.Coprime l := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop))
    obtain ⟨ψ, hψ1, hψ2⟩ := X.j_hol
    have hpush : GlobalTheory.KA.push (redM l n m (N * N))
        (bTop X l n m N (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))) s y
        = X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y) := by

      simp only [GlobalTheory.KA.push, Tower.diam, map_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [bTop]
      exact GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X ε.injective ⟨ψ, hψ2, hψ1⟩ N l w hP.odd hP.five hcop hw _ hD.1 _ _
        (hB _ (shArg_mem_fixMu _ s y')).1
    rw [hpush]
    exact hφ
  · have h1 := (CongruenceSubgroup.Gamma1_mem N (gm 1)).mp (hG1 1)
    have h2 := CongruenceSubgroup.Gamma0_mem.mp hD.1.1
    have h3 := hD.2
    have hdet := congrArg (fun z : ℤ => (z : ZMod N)) (Matrix.SpecialLinearGroup.det_coe (sgD N l (δ : ZMod N).val))
    simp only [Matrix.det_fin_two] at hdet
    unfold GlobalTheory.KZ.en at h3 ⊢
    push_cast at hdet h3 ⊢
    rw [ZMod.natCast_zmod_val] at h3
    rw [ZMod.natCast_zmod_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1.1, h2, mul_zero, add_zero, one_mul]
    rw [h2, mul_zero, sub_zero, h3] at hdet
    exact (Units.eq_inv_of_mul_eq_one_right hdet).symm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thcocd

section

@[expose] public section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

theorem UpperTheory.Kd.L.thcocd :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
      ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)),
      1 < c → 1 < d → Nat.Coprime c (6 * l * N) → Nat.Coprime d (6 * l * N) → 1 ≤ e →
      (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
          (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
            (t : ZMod l) • ![(r₀ : ZMod l), -1]) →
      (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) →
      ∀ (pr : X.Fn l → Fin 2 → Qbar l) (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
      ∃ (c₁ : ℕ) (κ₀ : Qbar l), κ₀ ≠ 0 ∧ ∀ (x : ZMod N) (δ : ℕ), Nat.Coprime δ N →
      ∀ (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
        (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e + 1) gm σ) (bB σ)) →
        ∀ (y : (ZMod (l ^ m))ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧
        ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → ∀ (φ : HahnSeries ℚ Ω),
        GlobalTheory.Glue.IsThB X A N l n
          (X.diam N l δ (GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
            X.galB l (repM (topM l n m (N * N)) y')
              (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y)) φ →
        ∀ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt →
        ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
        ∀ i : ℕ,
          Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j φ i)
            ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ₀ * ((tt.val : ℕ) : Qbar l) * (l : Qbar l) ^ m *
                j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m) (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
                  ((x.val : ℤ) * t * ((((δ : ZMod N)⁻¹).val : ℕ) : ℤ), 0) (t * ((((δ : ZMod N)⁻¹).val : ℕ) : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
                  ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i)) +
              (j (s (g.coeff (i : ℚ))) - j (g.coeff (i : ℚ)))) := by
  intro Ω _ _ _ ε X l _ hl2 hj A j hOver hjA N _ hN c d e gm hc hd hcc hdc he _hrow _hN10 pr α hAdm
  have hl : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hl.ne_zero
  haveI : NeZero l := ⟨hl0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl0⟩
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => IsSepClosed.hasEnoughRootsOfUnity_pow Ω l i
  have hw : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hw2 : 2 * e - 1 + 2 = 2 * e + 1 := by omega
  obtain ⟨c₁, κ, hκ, H⟩ := UpperTheory.Kd.L.twist l N (2 * e - 1) hw
  refine ⟨c₁, (κ : Qbar l), by exact_mod_cast hκ, ?_⟩
  intro x δ hδ m n c₀ hm hmn bB hB y
  have hG1 : ∀ r : (ZMod l)ˣ, gm r ∈ CongruenceSubgroup.Gamma1 N := fun r => (hAdm.2.2.1 r).1
  have hP : Par l N c d gm := by
    refine ⟨hl2, hAdm.1, hN, hc, hd, hcc, hdc, fun r => ?_, fun r => ?_, fun r => (hAdm.2.2.1 r).2⟩
    · exact CongruenceSubgroup.Gamma0_mem.mpr ((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 r)).2.2
    · simp only [GlobalTheory.KZ.en]
      rw [((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 r)).1, ((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 1)).1]
  have hlA : ((l : ℕ) : Ω) ∈ A.nonunits := by
    obtain ⟨v, hv, hlv⟩ := hOver
    rw [ValuationSubring.mem_nonunits_iff]
    have := (hv (l : 𝓞 ℚ)).mpr (by exact_mod_cast hlv)
    simpa using this
  have hB' : ∀ σ ∈ fixMu Ω (topMu l n m N),
      LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e - 1 + 2) gm σ) (bB σ) := by
    rw [hw2]; exact hB
  set δu : (ZMod N)ˣ := ZMod.unitOfCoprime δ hδ with hδu
  obtain ⟨g, hgA, hg⟩ := H ε X c d gm hP hG1 A hlA x m n c₀ hm hmn bB hB' y δu
  refine ⟨g, hgA, ?_⟩
  intro s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have hStab : GlobalTheory.Glue.Stab A s := fun z => apply_mem_iff_of_mem_Dec (F := ℚ) hs.1 z
  have hval : ∀ a ∈ A, A.valuation (s a - a) < 1 := fun a ha => hs.2 a ((A.valuation_le_one_iff a).mpr ha)
  have hzt : s (GlobalTheory.Glue.zt ε l m) = GlobalTheory.Glue.zt ε l m :=
    GlobalTheory.Col.fix_of_cycMod le_rfl hcyc (GlobalTheory.Glue.IsNTr.isPrimitiveRoot_zt ε l m).pow_eq_one
  have hsg : sgD N l ((δu : ZMod N).val) = sgD N l δ := by
    unfold sgD
    congr 1
    funext γ
    simp [IsDiam, hδu]
  have hφ' : GlobalTheory.Glue.IsThB X A N l n (X.diam N l (δu : ZMod N).val
      (GlobalTheory.KA.push (redM l n m (N * N)) (UpperTheory.Kd.L.bTop X l n m N bB) s y)) φ := by
    rw [show X.diam N l ((δu : ZMod N).val) = X.diam N l δ by unfold Tower.diam; rw [hsg]]
    exact hφ
  have key := hg s hStab hval hzt φ hφ' tt htt β t hβy hβ1 hlt i
  have hinv : ((δu⁻¹ : (ZMod N)ˣ) : ZMod N) = (δ : ZMod N)⁻¹ := by
    rw [← ZMod.inv_coe_unit, hδu, ZMod.coe_unitOfCoprime]
  rw [hinv, hw2] at key
  have gen : ∀ a b : Ω, GlobalTheory.Glue.CgA A l n a b → Cg n (j a) (j b) := by
    rintro a b ⟨z, hz, h⟩
    unfold Cg
    rw [← map_sub, h, map_mul, map_pow, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hjA z).mp hz)
  have := gen _ _ key
  clear H hg hB hB' hφ hφ' _hrow key gen hsg hStab hval hzt hP hG1 hAdm hlA hjA hj hOver
  convert this using 2
  · simp [GlobalTheory.KummerEisensteinGalois.seqN]
  · simp only [map_add (f := _), map_mul, map_sub, map_pow, map_natCast, map_ratCast]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thdiam

section

@[expose] public section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

theorem UpperTheory.Kd.L.thdiam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
      ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)),
      1 < c → 1 < d → Nat.Coprime c (6 * l * N) → Nat.Coprime d (6 * l * N) → 1 ≤ e →
      (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
          (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
            (t : ZMod l) • ![(r₀ : ZMod l), -1]) →
      (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) →
      ∀ (pr : X.Fn l → Fin 2 → Qbar l) (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
      ∃ (c₁ : ℕ) (κ₀ : Qbar l), κ₀ ≠ 0 ∧ ∀ (x : ZMod N),
      ∀ (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
        (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e + 1) gm σ) (bB σ)) →
        ∀ (y : (ZMod (l ^ m))ˣ) (δ : (ZMod N)ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧
        ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → ∀ (φ : HahnSeries ℚ Ω),
        GlobalTheory.Glue.IsThB X A N l n
          (X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
            X.galB l (repM (topM l n m (N * N)) y')
              (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y)) φ →
        ∀ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt →
        ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
        ∀ i : ℕ,
          Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j φ i)
            ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ₀ * ((tt.val : ℕ) : Qbar l) * (l : Qbar l) ^ m *
                j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m) (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
                  ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
                  ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i)) +
              (j (s (g.coeff (i : ℚ))) - j (g.coeff (i : ℚ)))) := by
  intro Ω _ _ _ ε X l _ hl2 hj A j hOver hjA N _ hN c d e gm hc hd hcc hdc he hrow hN10 pr α hAdm
  obtain ⟨c₁, κ₀, hκ, H⟩ := UpperTheory.Kd.L.thcocd Ω ε X l hl2 hj A j hOver hjA N hN c d e gm hc hd hcc hdc he
    hrow hN10 pr α hAdm
  refine ⟨c₁, κ₀, hκ, ?_⟩
  intro x m n c₀ hm hmn bB hB y δ
  obtain ⟨g, hgA, hg⟩ := H x (δ : ZMod N).val (ZMod.val_coe_unit_coprime δ) m n c₀ hm hmn bB hB y
  refine ⟨g, hgA, ?_⟩
  intro s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have key := hg s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have hinv : (((δ : ZMod N).val : ZMod N))⁻¹ = ((δ⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    rw [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
  rw [hinv] at key
  exact key
end
end
