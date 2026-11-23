module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTowerStatement
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientReductionBijectiveOfFlatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoZeroSub

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatLevel

theorem exists_trivial_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : A) (y : M) (h : f • y = 0) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → M), y = ∑ j, u j • v j ∧ ∀ j, f * u j = 0 := by
  classical
  have h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0 := by simpa using h
  obtain ⟨n, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, fun j => a () j, z, ?_, fun j => ?_⟩
  · simpa using hx ()
  · simpa using ha j

theorem exists_mul_of_flat {W B : Type} [CommRing W] [CommRing B] {t : W} (ht : t ∈ nonZeroDivisors W)
    {a b m : ℕ} (h : a + b = m) (c : W ⧸ Ideal.span {t ^ m} →+* B) (hc : c.Flat) (y : B)
    (hy : c (Ideal.Quotient.mk _ (t ^ b)) * y = 0) : ∃ z, c (Ideal.Quotient.mk _ (t ^ a)) * z = y := by
  let _ := c.toAlgebra
  have : Module.Flat (W ⧸ Ideal.span {t ^ m}) B := hc
  have hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0 := by
    rw [Algebra.smul_def]
    exact hy
  obtain ⟨n, u, v, hyv, hu⟩ := exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb
  have key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s) := by
    intro j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u j)
    have h1 := hu j
    rw [← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, hs⟩ := h1
    refine ⟨s, ?_⟩
    rw [← hw]
    congr 1
    have hb' : t ^ b ∈ nonZeroDivisors W := pow_mem ht b
    have h2 : (w - t ^ a * s) * t ^ b = 0 := by
      rw [← h, pow_add] at hs
      linear_combination (-1 : W) * hs
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)
  choose s hs using key
  refine ⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩
  rw [hyv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]
  rfl

theorem natCast_mem_nonZeroDivisors (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    (l : WittVector l k) ∈ nonZeroDivisors (WittVector l k) := by
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

set_option backward.isDefEq.respectTransparency false in
theorem flatL_Kt : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  intro l _ k _ _ _ O _ F ρ m
  show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))
  rw [CrystallineSemistableComparison.Pb.LsG.modF_sW]
  intro i
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · funext s
    have h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change ((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})
      ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0
    rw [h0, map_zero, zero_mul]
  · have key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i,
        ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)),
          (l : WittVector l k) ^ a • z = x s := by
      intro s
      have hs : (s.obj (Fin.last i)).obj.i.Flat := (s.obj (Fin.last i)).property
      have h0 : (l : WittVector l k) ^ b • x s = 0 := congrFun hx s
      obtain ⟨z, hz⟩ := exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab
        (s.obj (Fin.last i)).obj.i hs (x s) h0
      exact ⟨z, hz⟩
    choose z hz using key
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    exact ⟨z, funext fun s => hz s⟩

end GlobalTheory.CompanionTheory.FlatLevel

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevelStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.flat_witt_tower_level : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  first | exact @GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | exact GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | (intros; apply GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos

section

@[expose] public section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerSeq

theorem lseq_transport : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W)
    (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)),
    (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) →
    LSeq l S S' → Nonempty (LSeq l T T') := by
  intro W _ l S S' T T' e e' h h' L
  let E : ∀ n, S.M n ≃ₗ[W] T.M n := fun n => LinearEquiv.ofBijective (e.f n) (h n)
  let E' : ∀ n, S'.M n ≃ₗ[W] T'.M n := fun n => LinearEquiv.ofBijective (e'.f n) (h' n)
  have hc : ∀ n y, T.r n (E (n + 1) y) = E n (S.r n y) := fun n y => e.comm n y
  have hc' : ∀ n y, T'.r n (E' (n + 1) y) = E' n (S'.r n y) := fun n y => e'.comm n y
  have hr : ∀ n x, (E n).symm (T.r n x) = S.r n ((E (n + 1)).symm x) := by
    intro n x
    apply (E n).injective
    rw [LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]
  refine ⟨{
    ρ := fun c b => (E b).toLinearMap ∘ₗ L.ρ c b ∘ₗ (E c).symm.toLinearMap
    ν := fun a c => (E c).toLinearMap ∘ₗ L.ν a c ∘ₗ (E a).symm.toLinearMap
    δ := fun b a => (E' a).toLinearMap ∘ₗ L.δ b a ∘ₗ (E b).symm.toLinearMap
    kill := ?_, ρ_self := ?_, ρ_succ := ?_, ν_ρ := ?_, ν_r := ?_, ex₁ := ?_, δ_r := ?_, ex₂ := ?_ }⟩
  · intro n x
    apply (E n).symm.injective
    rw [map_smul, L.kill, map_zero]
  · intro c x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_self, LinearEquiv.apply_symm_apply]
  · intro c b hb x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_succ c b hb, hr]
  · intro a c ha x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [L.ν_ρ a c ha, map_smul, LinearEquiv.apply_symm_apply]
  · intro a c ha y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc, L.ν_r a c ha, hr]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.ρ c b ((E c).symm x) = 0 := by
      apply (E b).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₁ a b c hcab _ h0
    refine ⟨E a y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · intro b a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc', L.δ_r]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.δ b a ((E b).symm x) = 0 := by
      apply (E' a).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₂ a b c hcab _ h0
    refine ⟨E c y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.TowerSeq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsosStatement

section

@[expose] public section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  first | exact @GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | exact GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | (intros; apply GlobalTheory.CompanionTheory.TowerSeq.lseq_transport <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.smooth_model_restriction_bijective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ m j, Function.Bijective (resF l (B.schFn M.p) r.ρ m j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatRes.flat_restriction | exact GlobalTheory.CompanionTheory.FlatRes.flat_restriction | (intros; apply GlobalTheory.CompanionTheory.FlatRes.flat_restriction <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.LsSeqEq

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsG

open CrystallineSemistableComparison.Ls

theorem seq_flat {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) : ∃ (ψ : ∀ n, Cx.Hom (Kt l (B.schFn M.p) r.ρ n) (quo l (Kt l (B.schFn M.p) r.ρ (n + 1)) n) (RingHom.id _))
      (_ : ∀ n j, Function.Bijective ((ψ n).mapH j)),
      (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) ∧
      ∀ n j x, (ψ n).mapH j (resF l (B.schFn M.p) r.ρ n j ((Wc.HS l (B.schFn M.p) r.ρ j).r n x)) =
        (prj l (Kt l (B.schFn M.p) r.ρ (n + 1)) n).mapH j (resF l (B.schFn M.p) r.ρ (n + 1) j x) := by
  obtain ⟨ψ, hψ, hc⟩ := LsQ.seqflat0_pf r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  exact ⟨ψ, hψ, fun m b h j => GlobalTheory.T.quotient_reduction_bijective_of_flat _ l _ _ m (ψ m) (hfl m) (hfl (m + 1)) (hψ m) b h j, hc⟩

theorem ls_seq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) :
    Nonempty (CrystallineSemistableComparison.Tw.LSeq l (Wc.HS l (B.schFn M.p) r.ρ j) (Wc.HS l (B.schFn M.p) r.ρ (j + 1))) := by
  obtain ⟨ψ, hψ, hq, hc⟩ := seq_flat r M hM
  have hf := GlobalTheory.T.smooth_model_restriction_bijective r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  have fwd : ∀ i n x, (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i).r n (resF l (B.schFn M.p) r.ρ (n + 1) i x) =
      resF l (B.schFn M.p) r.ρ n i ((Wc.HS l (B.schFn M.p) r.ρ i).r n x) := by
    intro i n x
    change (LinearEquiv.ofBijective _ (hψ n i)).symm ((prj l _ n).mapH i (resF l (B.schFn M.p) r.ρ (n + 1) i x)) = _
    rw [← hc n i x]
    exact (LinearEquiv.ofBijective _ (hψ n i)).symm_apply_apply _
  let E : ∀ i n, (Wc.HS l (B.schFn M.p) r.ρ i).M n ≃ₗ[WittVector l r.k] (Kt l (B.schFn M.p) r.ρ n).H i :=
    fun i n => LinearEquiv.ofBijective _ (hf n i)
  let e : ∀ i, Sys.Hom (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i) (Wc.HS l (B.schFn M.p) r.ρ i) (RingHom.id _) := fun i =>
    { f := fun n => (E i n).symm.toLinearMap
      comm := fun n y => by
        apply (E i n).injective
        change E i n ((Wc.HS l (B.schFn M.p) r.ρ i).r n ((E i (n + 1)).symm y)) = E i n ((E i n).symm _)
        rw [LinearEquiv.apply_symm_apply]
        have h1 := fwd i n ((E i (n + 1)).symm y)
        have h2 : resF l (B.schFn M.p) r.ρ (n + 1) i ((E i (n + 1)).symm y) = y := (E i (n + 1)).apply_symm_apply y
        exact h1.symm.trans (congrArg _ h2) }
  exact GlobalTheory.T.lseq_of_level_isos _ l _ _ _ _ (e j) (e (j + 1)) (fun n => (E j n).symm.bijective) (fun n => (E (j + 1) n).symm.bijective)
    (GlobalTheory.T.lseq_of_flat_tower _ l _ ψ hψ hfl hq j).some

end CrystallineSemistableComparison.Pb.LsG

end
end
end
