module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.SmulEqAlgebraMapMul
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.MulVecMemLf

section

@[expose] public section

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem emb_add (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add (f := _), coord_emb, coord_emb, coord_emb]

theorem emb_zero : emb b (0 : ι → B) = 0 := by
  apply coord_injective b; rw [map_zero, coord_emb]

theorem emb_neg (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]

theorem emb_sub (c c' : ι → B) : emb b (c - c') = emb b c - emb b c' := by
  apply coord_injective b; rw [map_sub, coord_emb, coord_emb, coord_emb]

theorem emb_nsmul (N : ℕ) (c : ι → B) : emb b (N • c) = N • emb b c := by
  apply coord_injective b; rw [map_nsmul, coord_emb, coord_emb]

theorem isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = {p | coord b (f p) = coord b (g p)} := by
    ext p; exact (coord_injective b).eq_iff.symm
  rw [this]; exact isClosed_eq hf hg

end General

namespace Cpt

variable (I : AutInst)

abbrev ιb : Type := Fin (Module.finrank I.F I.E)

abbrev bs : Module.Basis (ιb I) I.F I.E := Module.finBasis I.F I.E

abbrev Co : Type := Fin I.n → Fin I.n → ιb I → Af I.F

def matOf (P : Co I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => emb (bs I) (P i j)

theorem mulVec_mem_Lf (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

theorem isClosed_LfC (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F,
      (∀ j k, coord (bs I) (y j) k ∈ Ohat I.F) → d • y ∈ I.Lf) :
    IsClosed {w : Fin I.n → ιb I → Af I.F | (fun j => emb (bs I) (w j)) ∈ I.Lf} := by
  let S : AddSubgroup (Fin I.n → ιb I → Af I.F) :=
    { carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf}
      add_mem' := fun {w w'} hw hw' => by
        have : (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j) := by
          funext j; simp [emb_add]
        show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf
        rw [this]; exact I.Lf.add_mem hw hw'
      zero_mem' := by
        show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf
        have : (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0 := by
          funext j; simp [emb_zero]
        rw [this]; exact I.Lf.zero_mem
      neg_mem' := fun {w} hw => by
        have : (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j) := by
          funext j; simp [emb_neg]
        show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf
        rw [this]; exact I.Lf.neg_mem hw }
  have hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0 := by
    let U := {w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}
    have hU : IsOpen U := by
      have : U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F := by
        ext w; simp [U]
      rw [this]
      refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) :=
        continuous_const.mul ((continuous_apply k).comp (continuous_apply j))
      exact hc.isOpen_preimage _ isOpen_Ohat
    have h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U := fun j k => by simpa using ohat_zero
    refine Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_
    have hd0 : (d : I.F) ≠ 0 := by exact_mod_cast hd.ne'
    have := hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k))
      (fun j k => by rw [coord_emb]; exact hw j k)
    show (fun j => emb (bs I) (w j)) ∈ I.Lf
    convert this using 1
    funext j
    rw [Pi.smul_apply, ← emb_nsmul]
    congr 1; funext k
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]
  exact AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)

end Cpt

end PI.WAU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.IsCompactCset

section

@[expose] public section

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

theorem ctsA_fst (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.1 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))

theorem ctsA_snd (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.2 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

theorem ctsA_mulE {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => (f p * g p) i j) := by
  simp only [Matrix.mul_apply]
  exact ctsA_sum _ fun l _ => ctsA_mul (hf i l) (hg l j)

theorem ctsA_constE (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (i j : Fin I.n) :
    CtsA (bs I) (fun _ : Co I × Co I => M i j) := ctsA_const _

theorem ctsA_cTE {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => Formalism.UG.cT (sg I) (f p) i j) := by
  show CtsA (bs I) (fun p => Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (f p j i))
  exact ctsA_map _ (hf j i)

theorem isClosed_matEq {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) :
    IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = ⋂ i, ⋂ j, {p | f p i j = g p i j} := by
    ext p; simp [← Matrix.ext_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eqA (bs I) (hf i j) (hg i j)

theorem isClosed_lat (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) :
    IsClosed {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
  have : {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} =
      ⋂ l ∈ I.L, {p | f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
    ext; simp
  rw [this]
  refine isClosed_biInter fun l _ => ?_
  have hc : Continuous (fun p => fun j => coord (bs I) ((f p *ᵥ inclV (F := I.F) l) j)) := by
    refine continuous_pi fun j => ?_
    have : CtsA (bs I) (fun p => (f p *ᵥ inclV (F := I.F) l) j) := by
      simp only [Matrix.mulVec, dotProduct]
      exact ctsA_sum _ fun k _ => ctsA_mul (hf j k) (ctsA_const _)
    exact this
  have := (isClosed_LfC I d hd hlow).preimage hc
  convert this using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, emb_coord]

theorem isCompact_Cset (N d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsCompact (Cset I N) := by
  have hbox : IsCompact {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} := by
    have : {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} =
        (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) ×ˢ
          (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨fun i j k => (h i j k).1, fun i j k => (h i j k).2⟩,
        fun h i j k => ⟨h.1 i j k, h.2 i j k⟩⟩
    rw [this]
    have h3 := isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n =>
      isCompact_univ_pi fun _ : ιb I => isCompact_Bx I N
    exact h3.prod h3
  have hf := ctsA_fst I
  have hs := ctsA_snd I
  have hc1 := isClosed_matEq I (ctsA_mulE I hf hs) (ctsA_constE I 1)
  have hc2 := isClosed_matEq I (ctsA_mulE I hs hf) (ctsA_constE I 1)
  have hc3 := isClosed_matEq I (ctsA_mulE I (ctsA_mulE I (ctsA_cTE I hf) (ctsA_constE I (Jf I))) hf)
    (ctsA_constE I (Jf I))
  have hc4 := isClosed_lat I d hd hlow hf
  have hc5 := isClosed_lat I d hd hlow hs
  exact hbox.inter_right (hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5))))

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

theorem psi_mem (N : ℕ) (p : Cset I N) : psi I N p ∈ I.Kset := by
  intro y
  have h1 := mulVec_mem_Lf I _ p.2.2.2.2.2.1
  have h2 := mulVec_mem_Lf I _ p.2.2.2.2.2.2
  show y ∈ I.Lf ↔ matOf I p.1.1 *ᵥ y ∈ I.Lf
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, p.2.2.2.1, Matrix.one_mulVec] at this

end Cpt

end PI.WAU
end
end
end
