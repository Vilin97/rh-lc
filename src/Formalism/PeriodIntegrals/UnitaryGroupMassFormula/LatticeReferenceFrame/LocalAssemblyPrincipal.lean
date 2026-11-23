module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.NatCastSmulMemL
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.SpanSmulInto

section

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem GE_star (g : ℕ) {x : I.E} (h : GE I g x) : GE I g (star x) := by
  obtain ⟨t, ht⟩ := h
  have hint : IsIntegral ℤ (starRingEnd I.E (t : I.E)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
    | exact (t.2).map (starRingEnd I.E).toIntAlgHom
  refine ⟨⟨starRingEnd I.E (t : I.E), hint⟩, ?_⟩
  rw [ht]
  first
  | (rw [star_mul', star_natCast]; rfl)
  | simp [star_mul']

theorem span_part (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M T : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E)
    (hM : Nat.Coprime M p) (hM0 : (M : I.E) ≠ 0) (hT : Nat.Coprime T p) (hT0 : (T : I.E) ≠ 0)
    (hθ1 : GE I (p ^ m) ((θ : I.E) * θ - θ)) (hθ2 : GE I (p ^ m) ((θ : I.E) * star (θ : I.E)))
    (hθ3 : GE I (p ^ m) (1 - (θ : I.E) - star (θ : I.E)))
    (hw : ∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p)
    (hspan : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd))
    (Sset : Set (Fin I.n → I.E))
    (hSe : ∀ a, M • e a ∈ Sset) (hSf : ∀ a, M • f a ∈ Sset)
    (hSz : (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) ∈ Sset)
    (hSb : ∀ i : Fin k, (θ : I.E) • ((T : I.E) • w i.castSucc) ∈ Sset)
    (hSbd : ∀ i : Fin k, star (θ : I.E) • ((T : I.E) • wd i.castSucc) ∈ Sset) :
    ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) := by
  classical
  set N : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) with hN
  have hsm : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), c • v = (c : I.E) • v := fun c v => rfl
  have hS : ∀ v ∈ Sset, v ∈ N := fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hE : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), v ∈ N → (c : I.E) • v ∈ N := fun c v hv => by
    rw [← hsm]
    exact N.smul_mem c hv
  have hnat : ∀ (s : ℕ) (v : Fin I.n → I.E), v ∈ N → (s : I.E) • v ∈ N := fun s v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv s
  have hgl : ∀ x ∈ I.L, ∀ t : 𝓞 I.E, (((p ^ m : ℕ) : I.E) * (t : I.E)) • x ∈ N := by
    intro x hx t
    have h1 : ((p ^ m : ℕ) : I.E) • x ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [mul_comm, mul_smul]
    exact hE t _ h1
  have hbez : ∀ z ∈ I.L, ∀ s : ℕ, Nat.Coprime s p → (s : I.E) • z ∈ N → z ∈ N := by
    intro z hz s hs hsz
    have hcop : IsCoprime (s : ℤ) ((p ^ m : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right m hs)
    obtain ⟨u, v, huv⟩ := hcop
    have hpz : ((p ^ m : ℕ) : I.E) • z ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩)
    have hc : (u : I.E) * (s : I.E) + (v : I.E) * ((p ^ m : ℕ) : I.E) = 1 := by
      have h := congrArg (Int.cast : ℤ → I.E) huv
      push_cast at h ⊢
      linear_combination h
    have e : z = u • ((s : I.E) • z) + v • (((p ^ m : ℕ) : I.E) • z) := by
      rw [← Int.cast_smul_eq_zsmul I.E u, ← Int.cast_smul_eq_zsmul I.E v, smul_smul, smul_smul,
        ← add_smul, hc, one_smul]
    rw [e]
    exact N.add_mem (zsmul_mem hsz u) (zsmul_mem hpz v)
  have hclr : ∀ v ∈ LA I p, ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
    intro v hv
    obtain ⟨s, hs, h⟩ := span_clear I p (I.L : Set (Fin I.n → I.E)) hv
    exact ⟨s, hs, by rwa [Submodule.span_eq] at h⟩
  have gen : ∀ (φ φ' : 𝓞 I.E) (u u' : Fin (k + 1) → Fin I.n → I.E),
      (∀ i, u i ∈ LA I p) → (∀ i, u' i ∈ LA I p) →
      (∀ i : Fin k, (φ : I.E) • ((T : I.E) • u i.castSucc) ∈ Sset) →
      (T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)) ∈ N →
      GE I (p ^ m) ((φ : I.E) * φ - φ) → GE I (p ^ m) ((φ : I.E) * φ') →
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range u) →
        (φ : I.E) • y ∈ N := by
    intro φ φ' u u' hu hu' hSu hz h1 h2 y hy hyA
    obtain ⟨s2, hs2, hs2L⟩ := hclr _ (hu (Fin.last k))
    obtain ⟨s3, hs3, hs3L⟩ := hclr _ (hu' (Fin.last k))
    obtain ⟨t1, ht1⟩ := h1
    obtain ⟨t2, ht2⟩ := h2
    obtain ⟨s1, hs1, hs1y⟩ := span_clear I p _ hyA
    have key : ∀ v ∈ Submodule.span (𝓞 I.E) (Set.range e ∪ Set.range f ∪ Set.range u),
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • v) ∈ N := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨i, rfl⟩
        · have h := hS _ (hSe a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • e a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • e a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · have h := hS _ (hSf a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • f a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • f a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · cases i using Fin.lastCases with
          | last =>
            have hA : ((M * s2 * s3 : ℕ) : I.E) •
                ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) ∈ N :=
              hnat _ _ (hE φ _ hz)
            have hB : ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                ((s2 : I.E) • u (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs2L t1)
            have hC : ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                ((s3 : I.E) • u' (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs3L t2)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u (Fin.last k)) =
                ((M * s2 * s3 : ℕ) : I.E) •
                  ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) -
                ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                  ((s2 : I.E) • u (Fin.last k))) +
                ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                  ((s3 : I.E) • u' (Fin.last k))) := by
              rw [← ht1, ← ht2]
              funext i
              simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              push_cast
              ring
            rw [e1]
            exact N.add_mem (N.sub_mem hA hB) hC
          | cast j =>
            have h := hS _ (hSu j)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u j.castSucc) =
                ((M * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((T : I.E) • u j.castSucc)) := by
              simp only [smul_smul]
              congr 1
              push_cast
              ring
            rw [e1]
            exact hnat _ _ h
      | zero => simp
      | add v w _ _ hv hw =>
        rw [smul_add, smul_add]
        exact N.add_mem hv hw
      | smul c v _ hv =>
        rw [hsm, smul_comm (φ : I.E) (c : I.E) v, smul_comm ((M * T * s2 * s3 : ℕ) : I.E) (c : I.E)]
        exact hE c _ hv
    have hk := key _ hs1y
    have hφy : (φ : I.E) • y ∈ I.L := by
      rw [← hsm]
      exact I.L.smul_mem φ hy
    refine hbez _ hφy (M * T * s2 * s3 * s1)
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left hM hT) hs2) hs3) hs1) ?_
    have e2 : ((M * T * s2 * s3 * s1 : ℕ) : I.E) • ((φ : I.E) • y) =
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((s1 : I.E) • y)) := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e2]
    exact hk
  obtain ⟨θb, hθb⟩ : ∃ θb : 𝓞 I.E, (θb : I.E) = star (θ : I.E) := by
    have hint : IsIntegral ℤ (starRingEnd I.E (θ : I.E)) := by
      first
      | exact (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
      | exact (θ.2).map (starRingEnd I.E).toIntAlgHom
    exact ⟨⟨starRingEnd I.E (θ : I.E), hint⟩, rfl⟩
  intro y hy
  have hyN1 : (θ : I.E) • y ∈ N :=
    gen θ θb w wd (fun i => (hw i).1) (fun i => (hw i).2) hSb (by rw [hθb]; exact hS _ hSz) hθ1
      (by rw [hθb]; exact hθ2) y hy (hspan y hy).1
  have hz2 : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) ∈ N := by
    have e : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) =
        -((T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k))) := by
      rw [hθb, ← smul_neg, neg_sub]
    rw [e]
    exact N.neg_mem (hS _ hSz)
  have h1' : GE I (p ^ m) ((θb : I.E) * θb - θb) := by
    have h := GE_star I (p ^ m) hθ1
    rwa [star_sub, star_mul', ← hθb] at h
  have h2' : GE I (p ^ m) ((θb : I.E) * θ) := by
    rw [hθb, mul_comm]
    exact hθ2
  have hyN2 : (θb : I.E) • y ∈ N :=
    gen θb θ wd w (fun i => (hw i).2) (fun i => (hw i).1) (fun i => by rw [hθb]; exact hSbd i) hz2 h1' h2'
      y hy (hspan y hy).2
  obtain ⟨t3, ht3⟩ := hθ3
  have h3 : ((1 : I.E) - θ - star (θ : I.E)) • y ∈ N := by
    rw [ht3]
    exact hgl y hy t3
  have e : y = (θ : I.E) • y + (θb : I.E) • y + ((1 : I.E) - θ - star (θ : I.E)) • y := by
    rw [hθb, ← add_smul, ← add_smul,
      show (θ : I.E) + star (θ : I.E) + (1 - θ - star (θ : I.E)) = 1 by ring, one_smul]
  rw [e]
  exact N.add_mem (N.add_mem hyN1 hyN2) h3

end PI.ScRefExists.PPA
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocalAssemblyPrincipal

section

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

def IsInt (I : Formalism.MainNotions.S.AutInst) (x : I.E) : Prop := ∃ a : 𝓞 I.E, (a : I.E) = x

section Int

variable (I : Formalism.MainNotions.S.AutInst)

theorem isInt_coe (a : 𝓞 I.E) : IsInt I (a : I.E) := ⟨a, rfl⟩

theorem isInt_mul {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

theorem isInt_sub {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

theorem isInt_add {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isInt_one : IsInt I (1 : I.E) := ⟨1, by simp⟩

theorem isInt_hG {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by
  obtain ⟨a, ha⟩ := (I.L_dual y).1 hy x hx
  exact ⟨a, ha⟩

theorem isInt_star (θ : 𝓞 I.E) : IsInt I (star (θ : I.E)) :=
  ⟨⟨star (θ : I.E), (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem natCast_mem_Ap (p s : ℕ) : (s : I.E) ∈ Ap I p := by
  refine ⟨1, Nat.coprime_one_left p, (s : 𝓞 I.E), ?_⟩
  simp

end Int

theorem local_assembly_principal : PPAssemble := by
  unfold PPAssemble
  intro I p m r k θ e f M w wd hp hm hH hw hew hwd hspan
  obtain ⟨-, -, hθ, -, -, -, -, hMc, -⟩ := hH
  obtain ⟨hθ1, hθ2, hθ3⟩ := hθ
  have hm0 : m ≠ 0 := by omega
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hMp : Nat.Coprime M p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p hm0) hMc
  have hM0 : (M : I.E) ≠ 0 := by
    have hM : M ≠ 0 := by
      rintro rfl
      exact hp1 ((Nat.coprime_zero_left _).1 hMp)
    exact_mod_cast hM

  choose sw hsw using fun i => LA_clear (I := I) p (hw i).1
  choose sd hsd using fun i => LA_clear (I := I) p (hw i).2
  have hT0p : Nat.Coprime ((∏ i, sw i) * ∏ i, sd i) p :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun i _ => (hsw i).1)
      (Nat.Coprime.prod_left fun i _ => (hsd i).1)
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ((∏ i, sw i) * ∏ i, sd i) ^ Nat.totient (p ^ m) := ⟨_, rfl⟩
  have hTp : Nat.Coprime T p := hTdef ▸ Nat.Coprime.pow_left _ hT0p
  have hT0dvd : ((∏ i, sw i) * ∏ i, sd i) ∣ T :=
    hTdef ▸ dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hp.pos m)).ne'
  have hTne : T ≠ 0 := by
    rintro h0
    rw [h0] at hTp
    exact hp1 ((Nat.coprime_zero_left _).1 hTp)
  have hTE : (T : I.E) ≠ 0 := by exact_mod_cast hTne
  have hTmod : T ≡ 1 [MOD p ^ m] := hTdef ▸ Nat.ModEq.pow_totient (Nat.Coprime.pow_right m hT0p)
  obtain ⟨c, hc⟩ : ∃ c, T = 1 + p ^ m * c := by
    have h1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hTne
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).1 hTmod.symm
    refine ⟨c, ?_⟩
    generalize p ^ m * c = q at hc ⊢
    omega
  have hT1 : QA I p (p ^ m) (1 - (T : I.E) ^ 2) := by
    apply QA_of_GE (I := I)
    refine ⟨-((c : 𝓞 I.E) + c + (p : 𝓞 I.E) ^ m * c * c), ?_⟩
    rw [hc]
    push_cast
    ring
  have hTA : (T : I.E) ^ 2 ∈ Ap I p := pow_mem (natCast_mem_Ap I p T) 2
  have hTw : ∀ i, (T : I.E) • w i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sw i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sw (Finset.mem_univ i))
      (dvd_mul_right _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsw i).2
  have hTwd : ∀ i, (T : I.E) • wd i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sd i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sd (Finset.mem_univ i))
      (dvd_mul_left _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsd i).2

  have hθ1s : GE I (p ^ m) (star (θ : I.E) * star (θ : I.E) - star (θ : I.E)) := by
    obtain ⟨t, ht⟩ := hθ1
    obtain ⟨ts, hts⟩ := isInt_star I t
    refine ⟨ts, ?_⟩
    have h := congrArg star ht
    simp only [star_sub, star_mul, star_natCast] at h
    rw [h, hts]
    ring
  obtain ⟨θs, hθs⟩ := isInt_star I θ
  obtain ⟨z, hzdef⟩ : ∃ z : Fin I.n → I.E,
      z = (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) := ⟨_, rfl⟩
  have hz : z ∈ I.L := by
    rw [hzdef, smul_sub, smul_comm (T : I.E) (θ : I.E), smul_comm (T : I.E) (star (θ : I.E)), ← hθs]
    exact I.L.sub_mem (I.L.smul_mem θ (hTw _)) (I.L.smul_mem θs (hTwd _))
  have hl1 : hG I (wd (Fin.last k)) (w (Fin.last k)) = 1 := by
    simpa using hwd (Fin.last k) (Fin.last k)
  have hl2 : hG I (w (Fin.last k)) (wd (Fin.last k)) = 1 := by
    rw [hG_symm (I := I) (wd (Fin.last k)) (w (Fin.last k)), hl1, star_one]
  have hl3 : ∀ i : Fin k, hG I (wd (Fin.last k)) (w i.castSucc) = 0 := by
    intro i
    rw [hwd, if_neg (Fin.castSucc_ne_last i).symm]
  have hl4 : ∀ i : Fin k, hG I (w (Fin.last k)) (wd i.castSucc) = 0 := by
    intro i
    rw [hG_symm (I := I) (wd i.castSucc) (w (Fin.last k)), hwd, if_neg (Fin.castSucc_ne_last i), star_zero]
  unfold Concl
  refine ⟨z, fun i => (T : I.E) • w i.castSucc, fun i => (T : I.E) • wd i.castSucc, hz,
    fun i => ⟨hTw _, hTwd _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hzdef]
    refine ⟨?_, ?_⟩ <;> rw [hG_smul_right, hG_sub_right, hG_smul_right, hG_smul_right]
    · rw [(hew a _).1, (hew a _).2.2.1]
      ring
    · rw [(hew a _).2.1, (hew a _).2.2.2]
      ring
  · intro a i
    simp [hG_smul_right, hew]
  ·
    apply GE_of_QA (I := I) p m (isInt_add I (isInt_hG I hz hz) (isInt_one I))
    have hzz : hG I z z + 1 =
        ((T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k))))
          * ((θ : I.E) * star (θ : I.E))
        - (T : I.E) ^ 2 * ((θ : I.E) * θ - θ)
        - (T : I.E) ^ 2 * (star (θ : I.E) * star (θ : I.E) - star (θ : I.E))
        + (T : I.E) ^ 2 * (1 - (θ : I.E) - star (θ : I.E))
        + (1 - (T : I.E) ^ 2) := by
      rw [hzdef]
      simp only [hG_smul_left, hG_smul_right, hG_sub_left, hG_sub_right, star_natCast, star_star, star_sub,
        star_smul]
      rw [hl1, hl2]
      ring
    rw [hzz]
    have hAD : (T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k)))
        ∈ Ap I p :=
      mul_mem hTA (add_mem (hG_mem_Ap (I := I) p (hw _).1 (hw _).1) (hG_mem_Ap (I := I) p (hw _).2 (hw _).2))
    refine QA_add (I := I) p _ (QA_add (I := I) p _ (QA_sub (I := I) p _ (QA_sub (I := I) p _
      (QA_mul (I := I) p _ hAD (QA_of_GE (I := I) p _ hθ2))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1s)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ3))) hT1
  · intro i
    constructor
    · apply GE_of_QA (I := I) p m (isInt_mul I (isInt_coe I θ) (isInt_hG I hz (hTw _)))
      have h : (θ : I.E) * hG I z ((T : I.E) • w i.castSucc) =
          ((T : I.E) ^ 2 * hG I (w (Fin.last k)) (w i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl3]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).1 (hw _).1))
        (QA_of_GE (I := I) p _ hθ2)
    · apply GE_of_QA (I := I) p m
        (isInt_mul I (by rw [← hθs]; exact isInt_coe I θs) (isInt_hG I hz (hTwd _)))
      have h : star (θ : I.E) * hG I z ((T : I.E) • wd i.castSucc) =
          -((T : I.E) ^ 2 * hG I (wd (Fin.last k)) (wd i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl4]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (neg_mem (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).2 (hw _).2)))
        (QA_of_GE (I := I) p _ hθ2)
  · intro i j
    have h : hG I ((T : I.E) • wd i.castSucc) ((T : I.E) • w j.castSucc) =
        (T : I.E) ^ 2 * (if i = j then 1 else 0) := by
      rw [hG_smul_left, hG_smul_right, hwd, star_natCast]
      simp only [Fin.castSucc_inj]
      ring
    rw [h]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one]
      apply GE_of_QA (I := I) p m
        (isInt_mul I (isInt_coe I θ) (isInt_sub I ⟨(T : 𝓞 I.E) ^ 2, by push_cast; rfl⟩ (isInt_one I)))
      have h2 : (θ : I.E) * ((T : I.E) ^ 2 - 1) = -(θ : I.E) * (1 - (T : I.E) ^ 2) := by ring
      rw [h2]
      exact QA_mul (I := I) p _ (neg_mem (int_mem_Ap (I := I) p θ)) hT1
    · rw [if_neg hij]
      exact ⟨0, by simp⟩
  · exact span_part (I := I) p m r k θ e f M T w wd hMp hM0 hTp hTE hθ1 hθ2 hθ3 hw hspan _
      (fun a => Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩))))
      (fun a => Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))
      (Or.inl (Or.inl (Or.inr hzdef.symm)))
      (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inr ⟨i, rfl⟩)

end PI.ScRefExists.PPA
end
end
end
