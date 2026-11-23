module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgD
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgE

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem collect {α β : Type} (S : Finset α) (X : Set β) (Q : α → Finset β → Prop)
    (hmono : ∀ a (F F' : Finset β), F ⊆ F' → Q a F → Q a F')
    (h : ∀ a ∈ S, ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ Q a F) :
    ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ ∀ a ∈ S, Q a F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨F, hF, hQ⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨F', hF', hQ'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨F ∪ F', by rw [Finset.coe_union]; exact Set.union_subset hF hF', fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hmono _ _ _ Finset.subset_union_right hQ'
    · exact hmono _ _ _ Finset.subset_union_left (hQ b hb)

theorem finGL_unip' {N k : ℕ} (x : BlockIx N k → Af E) :
    finGL E N (unip x) = unip (fun p => sFin E (x p)) := by
  apply Units.ext
  change 1 - (1 : Matrix (Fin N) (Fin N) (Af E)).map (sFin E) + (1 + nilM x).map (sFin E) = 1 + nilM _
  rw [Matrix.map_add _ (map_add (sFin E))]
  have : (nilM x).map (sFin E) = nilM (r := k) (fun p => sFin E (x p)) := by
    ext i j
    simp only [nilM, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this]; abel

theorem cover (L : Subgroup (GL (Fin (r + s)) (Af E))) (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) :
    ∃ Tf : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GL (Fin (r + s)) (Af E),
      ∃ (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)),
        t ∈ Tf ∧ l ∈ L ∧ g = unip x * lev (Af E) r s (a, b) * t * l := by
  obtain ⟨Tf, hTf⟩ := IwaAd.exists_finset_cover E (r + s) L hL
  refine ⟨Tf, fun g => ?_⟩
  obtain ⟨x, m, c, hc, rfl⟩ := IwaFin.exists_unip_lev_integral E r s g
  obtain ⟨t, ht, l, hl, rfl⟩ := hTf c hc
  exact ⟨x, m.1, m.2, t, l, ht, hl, by rw [← mul_assoc]⟩

theorem yp_decomp (k : Kinf E (r + s)) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E))
    (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)) :
    BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) * BlockDerivatives.yp k t * finGL E (r + s) l := by
  have hP : finGL E (r + s) (unip x * lev (Af E) r s (a, b)) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [map_mul, finGL_unip', Slice1.lev_finGL]
  rw [← hP, BlockDerivatives.yp, BlockDerivatives.yp]
  have e : finGL E (r + s) (unip x * lev (Af E) r s (a, b) * t * l) =
      finGL E (r + s) (unip x * lev (Af E) r s (a, b)) * finGL E (r + s) t * finGL E (r + s) l := by
    rw [map_mul, map_mul]
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E (r + s) (Unitary.toUnits k)) (finGL E (r + s) (unip x * lev (Af E) r s (a, b))),
    infGL_comm, mul_assoc]

theorem yp_one_fin {a : ℕ} (h : GL (Fin a) (Af E)) : BlockDerivatives.yp (1 : Kinf E a) h = finGL E a h := by
  simp [BlockDerivatives.yp]

theorem grp_step (m : GA E r × GA E s) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E))
    (y : GA E (r + s)) (z : GA E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * (unip (fun p => sFin E (x p)) *
        lev (Ad E) r s (finGL E r a, finGL E s b) * y * z) =
      unip v * (lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) * y) * z := by
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m (fun p => sFin E (x p))
  refine ⟨v, ?_⟩
  have e : lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) =
      lev (Ad E) r s m * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [← map_mul]; rfl
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (lev (Ad E) r s m) (unip _), hv]
  simp only [mul_assoc]

theorem slice_decomp_left (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₂ : GA E s) :
    sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₁ => ?_)
  have L : (sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₁ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [left_slice_apply, rt_apply]
  have R : (act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₁ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, left_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

theorem slice_decomp_right (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₁ : GA E r) :
    sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₂ => ?_)
  have L : (sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₂ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [right_slice_apply, rt_apply]
  have R : (act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₂ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, right_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFg

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem orbSpan_le {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) {φ : Sm E a} (hφ : φ ∈ V) :
    GlobalTheory.CuspRep.LocEx.orbSpan φ ≤ V :=
  Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)

theorem stepA_left (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, hb, -, he⟩ := hx
  have h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧
      b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r)) := fun i => Submodule.mem_span_finite_of_mem_span (hb i)
  choose Fi hFi hbFi using h
  refine ⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)
  · rw [left_slice_eq_sum (T β) b q he m₂]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
      (hbFi i)

theorem stepA_right (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, -, hq, he⟩ := hx
  refine ⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)
  · rw [right_slice_eq_sum (T β) b q he m₁]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))

theorem stepB_left (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂))
    (fun β hβ => stepA_left hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₂ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂
  exact hle hmem

theorem stepB_right (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁))
    (fun β hβ => stepA_right hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₁ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁
  exact hle hmem

theorem right_inv_of_stab (_hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) {ψ₀ : Sm E (r + s)} (hψ₀ : ψ₀ ∈ U)
    {l : GL (Fin (r + s)) (Af E)} (hl : l ∈ JFinTr.stabFin ψ₀) (y : GA E (r + s)) :
    (T ψ₀).1 (y * finGL E (r + s) l) = (T ψ₀).1 y := by
  have h1 : act (.fin l) ψ₀ = ψ₀ := hl
  have h2 := hT.equiv (.fin l) ψ₀ hψ₀
  rw [h1] at h2
  have h3 := congrArg (fun F : Sm E (r + s) => F.1 y) h2
  rw [act_fin_eq, rt_apply, yp_one_fin] at h3
  exact h3.symm

theorem stepC_left (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧ ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s),
      sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun t F F' hFF' h κ m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₂))
    (fun t _ => stepB_left hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₂ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]
  refine hW (.fin a) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem stepC_right (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧ ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r),
      sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun t F F' hFF' h κ m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₁))
    (fun t _ => stepB_right hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₁ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]
  refine hW (.fin b) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem LS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → BlockDerivatives.LS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E r)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_left hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mleft U T W :=
    hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₂, rfl⟩ := lsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₂

theorem RS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → BlockDerivatives.RS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E s)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_right hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mright U T W :=
    hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₁, rfl⟩ := rsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₁

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end
end
