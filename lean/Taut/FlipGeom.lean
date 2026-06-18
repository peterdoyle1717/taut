import Taut.Theorem2
import Taut.Ball

/-!
# Case-1 flip geometry (the missing `prime_step` packages) — AlephProver targets

The `prime_step` branch removes an eligible tet `e` from a taut filling `M` of the
2-sphere `σ`.  When the flipped edge is absent (`¬ FlipEdgePresent`, case 1) the new
boundary `σe := (σ \ sharedFaces M e) ∪ exposedFaces M e` is again a 2-sphere, the
removed filling `removeTet M e` is again taut, and gluing `e` back is a `GlueStep`.
These three facts — `IsSphere2 σe`, `IsTaut (removeTet M e)`, `GlueStep e σe σ` — are
the data the induction (`theorem3_core`) needs to recurse on the smaller filling and
then snoc `e` back.  The flip API in `Theorem2.lean` already supplies the support and
unit-chain facts (`support_flipBoundary_of_eligible`, `unitOn_flipBoundary_of_eligible`);
these are the remaining pieces.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- **Gluing the eligible tet back.** Pure set algebra (no `FlipEdgePresent` needed):
`e ∩ σe = exposedFaces M e` (card 2, type-2 glue) and `σ = σe △ tetFaces e`. -/
theorem glueStep_flipBoundary_of_eligible {M : Chain V} {σ : Finset (Finset V)}
    {e : Finset V} (hU : UnitOn (bdry M) σ) (he : EligibleTet M e) :
    GlueStep e ((σ \ sharedFaces M e) ∪ exposedFaces M e) σ := by
  have hsh_eq : sharedFaces M e = tetFaces e ∩ σ := by
    simp only [sharedFaces, hU.1]
  have hexp_mem : ∀ x, x ∈ exposedFaces M e ↔ (x ∈ tetFaces e ∧ x ∉ σ) := by
    intro x
    simp only [exposedFaces, hsh_eq, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  refine ⟨he.1, ?_, ?_⟩
  · -- shared: `tetFaces e ∩ σe = exposedFaces e`, of card 2
    right
    have heq : tetFaces e ∩ ((σ \ sharedFaces M e) ∪ exposedFaces M e) = exposedFaces M e := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      rw [hexp_mem x, hsh_eq]
      simp only [Finset.mem_inter]
      tauto
    rw [heq]; exact exposedFaces_card_of_eligible he
  · -- newBdry: `σ = (σe \ tetFaces e) ∪ (tetFaces e \ σe)` (a propositional tautology
    -- in `s ∈ σ`, `s ∈ tetFaces e` once `σe` membership is unfolded)
    ext s
    simp only [Finset.mem_union, Finset.mem_sdiff]
    rw [hexp_mem s, hsh_eq]
    simp only [Finset.mem_inter]
    tauto

/-- **Removing any tet preserves tautness.** `removeTet M e` is a sub-chain of `M`
(it zeroes one coefficient), and sub-chains of taut chains are taut
(`IsTaut.subChain`, Prop 1); eligibility/simpliciality are not needed. -/
theorem isTaut_removeTet {M : Chain V} {e : Finset V} (hT : IsTaut M) :
    IsTaut (removeTet M e) := by
  apply hT.subChain
  intro s
  simp only [removeTet, Finsupp.sub_apply, Finsupp.single_apply]
  by_cases hse : e = s
  · simp [hse]
  · simp [hse]

theorem connOn_erase_of_degree_two_bypass {G H : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {x p q : V}
    (hconn : ConnOn G S) (hpq : p ≠ q)
    (hClosed : ∀ {a b : V}, a ∈ S → G.Adj a b → b ∈ S)
    (hNbr : S.filter (fun y => G.Adj x y) = {p, q})
    (hHedge : H.Adj p q)
    (hPres : ∀ {a b : V}, a ∈ S.erase x → b ∈ S.erase x → G.Adj a b → H.Adj a b) :
    ConnOn H (S.erase x) := by
  classical
  unfold ConnOn at *
  let rec aux : (n : ℕ) → ∀ {u v : V}, (w : G.Walk u v) → w.length ≤ n → u ∈ S.erase x → v ∈ S.erase x → H.Reachable u v
    | 0, u, v, w, hlen, hu, hv => by
        have hzero : w.length = 0 := Nat.eq_zero_of_le_zero hlen
        have huv : u = v := SimpleGraph.Walk.eq_of_length_eq_zero hzero
        subst v
        exact SimpleGraph.Reachable.refl u
    | Nat.succ n, u, v, w, hlen, hu, hv => by
        cases w with
        | nil => exact SimpleGraph.Reachable.refl u
        | cons h qwalk =>
            rename_i y
            have hqLen : qwalk.length ≤ n := by
              simp [SimpleGraph.Walk.length] at hlen
              omega
            by_cases hyx : y = x
            · subst y
              cases qwalk with
              | nil =>
                  exfalso
                  exact (Finset.mem_erase.mp hv).1 rfl
              | cons h2 r =>
                  rename_i z
                  have hrLen : r.length ≤ n := by
                    simp [SimpleGraph.Walk.length] at hqLen
                    omega
                  have huS : u ∈ S := (Finset.mem_erase.mp hu).2
                  have hxS : x ∈ S := hClosed huS h
                  have hzS : z ∈ S := hClosed hxS h2
                  have hzErase : z ∈ S.erase x := Finset.mem_erase.mpr ⟨h2.ne.symm, hzS⟩
                  have hu_pq : u = p ∨ u = q := by
                    have huMem : u ∈ S.filter (fun y => G.Adj x y) := Finset.mem_filter.mpr ⟨huS, h.symm⟩
                    have huMem' : u ∈ ({p, q} : Finset V) := by
                      simpa only [hNbr] using huMem
                    simpa only [Finset.mem_insert, Finset.mem_singleton] using huMem'
                  have hz_pq : z = p ∨ z = q := by
                    have hzMem : z ∈ S.filter (fun y => G.Adj x y) := Finset.mem_filter.mpr ⟨hzS, h2⟩
                    have hzMem' : z ∈ ({p, q} : Finset V) := by
                      simpa only [hNbr] using hzMem
                    simpa only [Finset.mem_insert, Finset.mem_singleton] using hzMem'
                  have hreach_uz : H.Reachable u z := by
                    rcases hu_pq with hup | huq
                    · rcases hz_pq with hzp | hzq
                      · rw [hup, hzp]
                      · rw [hup, hzq]
                        exact SimpleGraph.Adj.reachable hHedge
                    · rcases hz_pq with hzp | hzq
                      · rw [huq, hzp]
                        exact SimpleGraph.Adj.reachable hHedge.symm
                      · rw [huq, hzq]
                  exact hreach_uz.trans (aux n r hrLen hzErase hv)
            · have huS : u ∈ S := (Finset.mem_erase.mp hu).2
              have hyS : y ∈ S := hClosed huS h
              have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hyS⟩
              have hHy : H.Adj u y := hPres hu hyErase h
              exact (SimpleGraph.Adj.reachable hHy).trans (aux n qwalk hqLen hyErase hv)
  intro a ha b hb
  have haS : a ∈ S := (Finset.mem_erase.mp ha).2
  have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
  rcases hconn a haS b hbS with ⟨w⟩
  exact aux w.length w (le_refl _) ha hb

theorem flipBoundary_card_faces_eq {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ((σ \ sharedFaces M e) ∪ exposedFaces M e).card = σ.card := by
  classical
  have hsub : sharedFaces M e ⊆ σ := by
    intro s hs
    unfold sharedFaces at hs
    rw [hU.1] at hs
    rw [Finset.mem_inter] at hs
    exact hs.2
  have hsharedcard : (sharedFaces M e).card = 2 := he.2.2.1
  have hsdiffcard : (σ \ sharedFaces M e).card = σ.card - 2 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_eq_left.2 hsub]
    rw [hsharedcard]
  have hexpcard : (exposedFaces M e).card = 2 := exposedFaces_card_of_eligible he
  have hdisj : Disjoint (σ \ sharedFaces M e) (exposedFaces M e) := by
    rw [Finset.disjoint_left]
    intro s hsσ hsExp
    rw [Finset.mem_sdiff] at hsσ
    exact hsσ.2 (by
      have hsTet : s ∈ tetFaces e := exposedFaces_subset_tetFaces M e hsExp
      unfold sharedFaces
      rw [hU.1]
      rw [Finset.mem_inter]
      exact ⟨hsTet, hsσ.1⟩)
  rw [Finset.card_union_of_disjoint hdisj]
  rw [hsdiffcard, hexpcard]
  have hle : 2 ≤ σ.card := by
    rw [← hsharedcard]
    exact Finset.card_le_card hsub
  omega

theorem flipBoundary_pure_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ∀ f ∈ ((σ \ sharedFaces M e) ∪ exposedFaces M e), f.card = 3 := by
  intro f hfmem
  rcases mem_union.mp hfmem with hleft | hright
  · exact hσ.pure f (mem_sdiff.mp hleft).1
  · have hsub := exposedFaces_subset_tetFaces M e
    have hf_tet : f ∈ tetFaces e := hsub hright
    unfold tetFaces at hf_tet
    exact (mem_powersetCard.mp hf_tet).2

theorem flipBoundary_verts_eq {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    vertsOf ((σ \ sharedFaces M e) ∪ exposedFaces M e) = vertsOf σ := by
  classical
  let S : Finset (Finset V) := sharedFaces M e
  let E : Finset (Finset V) := exposedFaces M e
  have hSσ : S ⊆ σ := by
    intro F hF
    dsimp [S] at hF
    rw [sharedFaces, hU.1] at hF
    exact (Finset.mem_inter.mp hF).2
  have hSverts : vertsOf S = e := by
    dsimp [S]
    have hsub : sharedFaces M e ⊆ tetFaces e := sharedFaces_subset_tetFaces M e
    have hcard : (sharedFaces M e).card = 2 := he.2.2.1
    ext x
    rw [mem_vertsOf]
    constructor
    · rintro ⟨F, hFA, hxF⟩
      exact (Finset.mem_powersetCard.mp (hsub hFA)).1 hxF
    · intro hxe
      obtain ⟨F₁, F₂, hne, hpair⟩ := Finset.card_eq_two.mp hcard
      have hF₁A : F₁ ∈ sharedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_self F₁ {F₂}
      have hF₂A : F₂ ∈ sharedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self F₂)
      by_contra hxnot
      have hxF₁ : x ∉ F₁ := by
        intro hx
        exact hxnot ⟨F₁, hF₁A, hx⟩
      have hxF₂ : x ∉ F₂ := by
        intro hx
        exact hxnot ⟨F₂, hF₂A, hx⟩
      have face_eq_erase : ∀ {F : Finset V}, F ∈ tetFaces e → x ∉ F → F = e.erase x := by
        intro F hFt hxnotF
        obtain ⟨hsubF, hcardF⟩ := Finset.mem_powersetCard.mp hFt
        have hsubErase : F ⊆ e.erase x := by
          intro y hy
          exact Finset.mem_erase.mpr ⟨by intro hyx; subst hyx; exact hxnotF hy, hsubF hy⟩
        have hcardErase : (e.erase x).card = 3 := by
          rw [Finset.card_erase_of_mem hxe, he.1]
        exact Finset.eq_of_subset_of_card_le hsubErase (by rw [hcardF, hcardErase])
      have hF₁eq : F₁ = e.erase x := face_eq_erase (hsub hF₁A) hxF₁
      have hF₂eq : F₂ = e.erase x := face_eq_erase (hsub hF₂A) hxF₂
      exact hne (hF₁eq.trans hF₂eq.symm)
  have hEverts : vertsOf E = e := by
    dsimp [E]
    have hsub : exposedFaces M e ⊆ tetFaces e := exposedFaces_subset_tetFaces M e
    have hcard : (exposedFaces M e).card = 2 := exposedFaces_card_of_eligible he
    ext x
    rw [mem_vertsOf]
    constructor
    · rintro ⟨F, hFA, hxF⟩
      exact (Finset.mem_powersetCard.mp (hsub hFA)).1 hxF
    · intro hxe
      obtain ⟨F₁, F₂, hne, hpair⟩ := Finset.card_eq_two.mp hcard
      have hF₁A : F₁ ∈ exposedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_self F₁ {F₂}
      have hF₂A : F₂ ∈ exposedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self F₂)
      by_contra hxnot
      have hxF₁ : x ∉ F₁ := by
        intro hx
        exact hxnot ⟨F₁, hF₁A, hx⟩
      have hxF₂ : x ∉ F₂ := by
        intro hx
        exact hxnot ⟨F₂, hF₂A, hx⟩
      have face_eq_erase : ∀ {F : Finset V}, F ∈ tetFaces e → x ∉ F → F = e.erase x := by
        intro F hFt hxnotF
        obtain ⟨hsubF, hcardF⟩ := Finset.mem_powersetCard.mp hFt
        have hsubErase : F ⊆ e.erase x := by
          intro y hy
          exact Finset.mem_erase.mpr ⟨by intro hyx; subst hyx; exact hxnotF hy, hsubF hy⟩
        have hcardErase : (e.erase x).card = 3 := by
          rw [Finset.card_erase_of_mem hxe, he.1]
        exact Finset.eq_of_subset_of_card_le hsubErase (by rw [hcardF, hcardErase])
      have hF₁eq : F₁ = e.erase x := face_eq_erase (hsub hF₁A) hxF₁
      have hF₂eq : F₂ = e.erase x := face_eq_erase (hsub hF₂A) hxF₂
      exact hne (hF₁eq.trans hF₂eq.symm)
  ext x
  rw [mem_vertsOf, mem_vertsOf]
  constructor
  · rintro ⟨F, hF, hxF⟩
    rw [Finset.mem_union] at hF
    rcases hF with hF | hF
    · exact ⟨F, (Finset.mem_sdiff.mp hF).1, hxF⟩
    · have hxE : x ∈ vertsOf E := mem_vertsOf.mpr ⟨F, hF, hxF⟩
      have hxe : x ∈ e := by simpa only [hEverts] using hxE
      have hxS : x ∈ vertsOf S := by simpa only [hSverts] using hxe
      obtain ⟨G, hGS, hxG⟩ := mem_vertsOf.mp hxS
      exact ⟨G, hSσ hGS, hxG⟩
  · rintro ⟨F, hFσ, hxF⟩
    by_cases hFS : F ∈ S
    · have hxS : x ∈ vertsOf S := mem_vertsOf.mpr ⟨F, hFS, hxF⟩
      have hxe : x ∈ e := by simpa only [hSverts] using hxS
      have hxE : x ∈ vertsOf E := by simpa only [hEverts] using hxe
      obtain ⟨G, hGE, hxG⟩ := mem_vertsOf.mp hxE
      exact ⟨G, by rw [Finset.mem_union]; exact Or.inr hGE, hxG⟩
    · exact ⟨F, by rw [Finset.mem_union]; exact Or.inl (Finset.mem_sdiff.mpr ⟨hFσ, hFS⟩), hxF⟩

theorem flipBoundary_conn_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ConnOn (skel ((σ \ sharedFaces M e) ∪ exposedFaces M e))
      (vertsOf ((σ \ sharedFaces M e) ∪ exposedFaces M e)) := by
  classical
  let τ : Finset (Finset V) := (σ \ sharedFaces M e) ∪ exposedFaces M e
  have hverts : vertsOf τ = vertsOf σ := by
    dsimp [τ]
    exact flipBoundary_verts_eq (M := M) (σ := σ) (e := e) (f₃ := f₃) (f₄ := f₄) hσ hU hS he hexp hf hNoFlip
  have ht4 : e.card = 4 := he.1
  have hshcard : (sharedFaces M e).card = 2 := he.2.2.1
  have hf3exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp [hf]
  have hf4exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp [hf]
  have hf3τ : f₃ ∈ τ := by
    dsimp [τ]
    exact Finset.mem_union.mpr (Or.inr hf3exp)
  have hf4τ : f₄ ∈ τ := by
    dsimp [τ]
    exact Finset.mem_union.mpr (Or.inr hf4exp)
  have hstep : ∀ {u v : V}, (skel σ).Adj u v → (skel τ).Reachable u v := by
    intro u v hadj
    obtain ⟨huv, hpσ⟩ := hadj
    by_cases hpτ : ({u, v} : Finset V) ∈ edgesOf τ
    · exact SimpleGraph.Adj.reachable (G := skel τ) ⟨huv, hpτ⟩
    · obtain ⟨g1, hg1σ, g2, hg2σ, hg12, hpg1, hpg2, huniq⟩ := exists_two_faces hσ.toClosedSurface hpσ
      have hpcard : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
      have hg1_notτ : g1 ∉ τ := by
        intro hg1τ
        exact hpτ (mem_edgesOf.mpr ⟨g1, hg1τ, hpg1, hpcard⟩)
      have hg2_notτ : g2 ∉ τ := by
        intro hg2τ
        exact hpτ (mem_edgesOf.mpr ⟨g2, hg2τ, hpg2, hpcard⟩)
      have hg1sh : g1 ∈ sharedFaces M e := by
        by_contra hns
        apply hg1_notτ
        dsimp [τ]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hg1σ, hns⟩))
      have hg2sh : g2 ∈ sharedFaces M e := by
        by_contra hns
        apply hg2_notτ
        dsimp [τ]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hg2σ, hns⟩))
      have hshared_eq : sharedFaces M e = {g1, g2} := by
        have hsub : ({g1, g2} : Finset (Finset V)) ⊆ sharedFaces M e := by
          intro s hs
          rw [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact hg1sh
          · exact hg2sh
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [hshcard, Finset.card_pair hg12])).symm
      have hcap_shared : g1 ∩ g2 = ({u, v} : Finset V) := by
        exact inter_eq_edge_of_two_faces (hσ.pure g1 hg1σ) (hσ.pure g2 hg2σ) hg12 hpcard hpg1 hpg2
      obtain ⟨c, hcp, hg1eq⟩ := exists_third hpg1 hpcard (hσ.pure g1 hg1σ)
      have hcg1 : c ∈ g1 := by rw [hg1eq]; exact Finset.mem_insert_self c _
      have hcg2_not : c ∉ g2 := by
        intro hcg2
        have : c ∈ g1 ∩ g2 := Finset.mem_inter.mpr ⟨hcg1, hcg2⟩
        rw [hcap_shared] at this
        exact hcp this
      have hcu : c ≠ u := by
        intro h; apply hcp; rw [h]; simp
      have hcv : c ≠ v := by
        intro h; apply hcp; rw [h]; simp
      have hue : u ∈ e := by
        have hg1tet := sharedFaces_subset_tetFaces M e hg1sh
        exact (Finset.mem_powersetCard.mp hg1tet).1 (hpg1 (by simp))
      have hve : v ∈ e := by
        have hg1tet := sharedFaces_subset_tetFaces M e hg1sh
        exact (Finset.mem_powersetCard.mp hg1tet).1 (hpg1 (by simp))
      have hce : c ∈ e := by
        have hg1tet := sharedFaces_subset_tetFaces M e hg1sh
        exact (Finset.mem_powersetCard.mp hg1tet).1 hcg1
      have erase_unique : ∀ {F : Finset V} {a : V}, F ∈ tetFaces e → a ∈ e → a ∉ F → F = e.erase a := by
        intro F a hFtet hae haF
        obtain ⟨y, hye, hF⟩ := exists_erase_eq_of_mem_tetFaces ht4 hFtet
        have hya : y = a := by
          by_contra hya
          apply haF
          rw [hF]
          exact Finset.mem_erase.mpr ⟨Ne.symm hya, hae⟩
        rw [hF, hya]
      have hf3tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf3exp
      have hf4tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf4exp
      have hf3nsh : f₃ ∉ sharedFaces M e := (Finset.mem_sdiff.mp hf3exp).2
      have hf4nsh : f₄ ∉ sharedFaces M e := (Finset.mem_sdiff.mp hf4exp).2
      have hc_f3 : c ∈ f₃ := by
        by_contra hcf3
        have hf3eq : f₃ = e.erase c := erase_unique hf3tet hce hcf3
        have hg2tet : g2 ∈ tetFaces e := sharedFaces_subset_tetFaces M e hg2sh
        have hg2eq : g2 = e.erase c := erase_unique hg2tet hce hcg2_not
        have hfg : f₃ = g2 := by rw [hf3eq, hg2eq]
        exact hf3nsh (by simpa [hfg] using hg2sh)
      have hc_f4 : c ∈ f₄ := by
        by_contra hcf4
        have hf4eq : f₄ = e.erase c := erase_unique hf4tet hce hcf4
        have hg2tet : g2 ∈ tetFaces e := sharedFaces_subset_tetFaces M e hg2sh
        have hg2eq : g2 = e.erase c := erase_unique hg2tet hce hcg2_not
        have hfg : f₄ = g2 := by rw [hf4eq, hg2eq]
        exact hf4nsh (by simpa [hfg] using hg2sh)
      have hu_exp : u ∈ f₃ ∨ u ∈ f₄ := by
        by_contra hnot
        have hnf3 : u ∉ f₃ := fun hu3 => hnot (Or.inl hu3)
        have hnf4 : u ∉ f₄ := fun hu4 => hnot (Or.inr hu4)
        have hf3eq : f₃ = e.erase u := erase_unique hf3tet hue hnf3
        have hf4eq : f₄ = e.erase u := erase_unique hf4tet hue hnf4
        exact hf (by rw [hf3eq, hf4eq])
      have hv_exp : v ∈ f₃ ∨ v ∈ f₄ := by
        by_contra hnot
        have hnf3 : v ∉ f₃ := fun hv3 => hnot (Or.inl hv3)
        have hnf4 : v ∉ f₄ := fun hv4 => hnot (Or.inr hv4)
        have hf3eq : f₃ = e.erase v := erase_unique hf3tet hve hnf3
        have hf4eq : f₄ = e.erase v := erase_unique hf4tet hve hnf4
        exact hf (by rw [hf3eq, hf4eq])
      have huc_edge : ({u, c} : Finset V) ∈ edgesOf τ := by
        rcases hu_exp with hu3 | hu4
        · refine mem_edgesOf.mpr ⟨f₃, hf3τ, ?_, Finset.card_pair (Ne.symm hcu)⟩
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hu3
          · exact hz ▸ hc_f3
        · refine mem_edgesOf.mpr ⟨f₄, hf4τ, ?_, Finset.card_pair (Ne.symm hcu)⟩
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hu4
          · exact hz ▸ hc_f4
      have hcv_edge : ({c, v} : Finset V) ∈ edgesOf τ := by
        rcases hv_exp with hv3 | hv4
        · refine mem_edgesOf.mpr ⟨f₃, hf3τ, ?_, Finset.card_pair hcv⟩
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hc_f3
          · exact hz ▸ hv3
        · refine mem_edgesOf.mpr ⟨f₄, hf4τ, ?_, Finset.card_pair hcv⟩
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hc_f4
          · exact hz ▸ hv4
      exact (SimpleGraph.Adj.reachable (G := skel τ) ⟨Ne.symm hcu, huc_edge⟩).trans
        (SimpleGraph.Adj.reachable (G := skel τ) ⟨hcv, hcv_edge⟩)
  have lift_walk : ∀ {a b : V}, (skel σ).Walk a b → (skel τ).Reachable a b := by
    intro a b p
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj p ih => exact (hstep hadj).trans ih
  intro x hx y hy
  have hxσ : x ∈ vertsOf σ := by simpa [τ] using (hverts ▸ hx)
  have hyσ : y ∈ vertsOf σ := by simpa [τ] using (hverts ▸ hy)
  obtain ⟨p⟩ := hσ.conn x hxσ y hyσ
  exact lift_walk p

theorem sharedFaces_eq_tetFaces_inter_sigma {M : Chain V} {σ : Finset (Finset V)} {e : Finset V}
    (hU : UnitOn (bdry M) σ) :
    sharedFaces M e = tetFaces e ∩ σ := by
  simp only [sharedFaces, hU.1]

theorem mem_exposedFaces_iff_tetFace_not_sigma {M : Chain V} {σ : Finset (Finset V)} {e : Finset V}
    (hU : UnitOn (bdry M) σ) :
    ∀ f, f ∈ exposedFaces M e ↔ f ∈ tetFaces e ∧ f ∉ σ := by
  intro f
  unfold exposedFaces
  rw [sharedFaces_eq_tetFaces_inter_sigma hU]
  simp only [mem_sdiff, mem_inter]
  tauto

theorem tetFaces_edge_filter_card_eq_two {e a : Finset V} (he : e.card = 4) (hae : a ⊆ e) (hacard : a.card = 2) :
    ((tetFaces e).filter (fun F => a ⊆ F)).card = 2 := by
  classical
  have hfilter : (tetFaces e).filter (fun F => a ⊆ F)
      = (e \ a).image (fun z => insert z a) := by
    ext F
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hf, haF⟩
      rw [tetFaces, Finset.mem_powersetCard] at hf
      obtain ⟨hsub, hcardF⟩ := hf
      have hd : (F \ a).card = 1 := by
        rw [Finset.card_sdiff_of_subset haF, hcardF, hacard]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hd
      have hzf : z ∈ F \ a := by rw [hz]; exact Finset.mem_singleton_self z
      obtain ⟨hzF, hza⟩ := Finset.mem_sdiff.mp hzf
      refine ⟨z, Finset.mem_sdiff.mpr ⟨hsub hzF, hza⟩, ?_⟩
      have : F = a ∪ (F \ a) := by
        rw [Finset.union_sdiff_of_subset haF]
      rw [this, hz]
      ext x
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      tauto
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hze, hza⟩ := Finset.mem_sdiff.mp hz
      refine ⟨?_, Finset.subset_insert z a⟩
      rw [tetFaces, Finset.mem_powersetCard]
      refine ⟨Finset.insert_subset hze hae, ?_⟩
      rw [Finset.card_insert_of_notMem hza, hacard]
  rw [hfilter, Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hae, he, hacard]
  intro z₁ h₁ z₂ h₂ hins
  have hins' : insert z₁ a = insert z₂ a := hins
  have hz₁ : z₁ ∈ insert z₂ a := hins' ▸ Finset.mem_insert_self z₁ a
  rcases Finset.mem_insert.mp hz₁ with h | h
  · exact h
  · exact absurd h (Finset.mem_sdiff.mp h₁).2

theorem flipBoundary_closed_edge_in_tet_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ a : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄)
    (haτ : a ∈ edgesOf ((σ \ sharedFaces M e) ∪ exposedFaces M e)) (hae : a ⊆ e) :
    edgeDeg ((σ \ sharedFaces M e) ∪ exposedFaces M e) a = 2 := by
  classical
  let P : Finset V → Prop := fun F => a ⊆ F
  have hacard : a.card = 2 := card_of_mem_edgesOf haτ
  have hTcard : ((tetFaces e).filter P).card = 2 :=
    tetFaces_edge_filter_card_eq_two he.1 hae hacard
  have hsh_mem : ∀ F, F ∈ sharedFaces M e ↔ F ∈ tetFaces e ∧ F ∈ σ := by
    intro F
    rw [sharedFaces_eq_tetFaces_inter_sigma hU]
    simp only [Finset.mem_inter]
  have hT_eq : (tetFaces e).filter P = (sharedFaces M e).filter P ∪ (exposedFaces M e).filter P := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hFt, hP⟩
      by_cases hFs : F ∈ sharedFaces M e
      · exact Or.inl ⟨hFs, hP⟩
      · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hFt, hFs⟩, hP⟩
    · rintro (⟨hFs, hP⟩ | ⟨hFe, hP⟩)
      · exact ⟨sharedFaces_subset_tetFaces M e hFs, hP⟩
      · exact ⟨exposedFaces_subset_tetFaces M e hFe, hP⟩
  have hdisj : Disjoint ((sharedFaces M e).filter P) ((exposedFaces M e).filter P) := by
    rw [Finset.disjoint_left]
    intro F hFs hFe
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hFe).1).2 (Finset.mem_filter.mp hFs).1
  have hsum : ((sharedFaces M e).filter P).card + ((exposedFaces M e).filter P).card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hT_eq, hTcard]
  have hshared_sub_sigma_filter : (sharedFaces M e).filter P ⊆ σ.filter P := by
    intro F hF
    exact Finset.mem_filter.mpr ⟨(hsh_mem F).mp (Finset.mem_filter.mp hF).1 |>.2, (Finset.mem_filter.mp hF).2⟩
  have hOldCard : (σ.filter P \ sharedFaces M e).card = (σ.filter P).card - ((sharedFaces M e).filter P).card := by
    have hsdiff_eq : σ.filter P \ sharedFaces M e = σ.filter P \ (sharedFaces M e).filter P := by
      ext F
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [hsdiff_eq]
    exact Finset.card_sdiff_of_subset hshared_sub_sigma_filter
  have hτcard : edgeDeg ((σ \ sharedFaces M e) ∪ exposedFaces M e) a =
      (σ.filter P \ sharedFaces M e).card + ((exposedFaces M e).filter P).card := by
    rw [edgeDeg]
    have hfilter : (((σ \ sharedFaces M e) ∪ exposedFaces M e).filter P) =
        (σ.filter P \ sharedFaces M e) ∪ ((exposedFaces M e).filter P) := by
      ext F
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [hfilter]
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro F hOld hExp
    have hFσ : F ∈ σ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hOld).1).1
    have hnσ : F ∉ σ := ((mem_exposedFaces_iff_tetFace_not_sigma hU F).mp (Finset.mem_filter.mp hExp).1).2
    exact hnσ hFσ
  have hf3exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  have hf4exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  have hf3tet : f₃ ∈ tetFaces e := ((mem_exposedFaces_iff_tetFace_not_sigma hU f₃).mp hf3exp).1
  have hf4tet : f₄ ∈ tetFaces e := ((mem_exposedFaces_iff_tetFace_not_sigma hU f₄).mp hf4exp).1
  have edge_of_shared_pos : 0 < ((sharedFaces M e).filter P).card → a ∈ edgesOf σ := by
    intro hpos
    obtain ⟨F, hF⟩ := Finset.card_pos.mp hpos
    exact mem_edgesOf.mpr ⟨F, (hsh_mem F).mp (Finset.mem_filter.mp hF).1 |>.2,
      (Finset.mem_filter.mp hF).2, hacard⟩
  by_cases h3 : P f₃
  · by_cases h4 : P f₄
    · have hEcard : ((exposedFaces M e).filter P).card = 2 := by
        rw [hexp]
        have heq : ({f₃, f₄} : Finset (Finset V)).filter P = {f₃, f₄} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro h; exact h.1
          · intro h
            rcases h with rfl | rfl
            · exact ⟨Or.inl rfl, h3⟩
            · exact ⟨Or.inr rfl, h4⟩
        rw [heq, Finset.card_pair hf]
      have hShcard : ((sharedFaces M e).filter P).card = 0 := by omega
      have hf3card : f₃.card = 3 := (Finset.mem_powersetCard.mp hf3tet).2
      have hf4card : f₄.card = 3 := (Finset.mem_powersetCard.mp hf4tet).2
      have hinter : f₃ ∩ f₄ = a := inter_eq_edge_of_two_faces hf3card hf4card hf hacard h3 h4
      have hnotσ : a ∉ edgesOf σ := by
        intro haσ
        exact hNoFlip (by
          unfold FlipEdgePresent
          rw [hinter]
          exact haσ)
      have hσempty : σ.filter P = ∅ := by
        ext F
        constructor
        · intro hF
          exact False.elim (hnotσ (mem_edgesOf.mpr ⟨F, (Finset.mem_filter.mp hF).1, (Finset.mem_filter.mp hF).2, hacard⟩))
        · intro hF
          cases hF
      have hσcard : (σ.filter P).card = 0 := by
        rw [hσempty, Finset.card_empty]
      rw [hτcard, hOldCard, hσcard, hShcard, hEcard]
    · have hEcard : ((exposedFaces M e).filter P).card = 1 := by
        rw [hexp]
        have heq : ({f₃, f₄} : Finset (Finset V)).filter P = {f₃} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact rfl
            · exact False.elim (h4 hP)
          · intro hF
            rw [hF]
            exact ⟨Or.inl rfl, h3⟩
        rw [heq, Finset.card_singleton]
      have hShcard : ((sharedFaces M e).filter P).card = 1 := by omega
      have haσ : a ∈ edgesOf σ := edge_of_shared_pos (by omega)
      have hσcard : (σ.filter P).card = 2 := by
        simpa only [edgeDeg, P] using hσ.closed a haσ
      rw [hτcard, hOldCard, hσcard, hShcard, hEcard]
  · by_cases h4 : P f₄
    · have hEcard : ((exposedFaces M e).filter P).card = 1 := by
        rw [hexp]
        have heq : ({f₃, f₄} : Finset (Finset V)).filter P = {f₄} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact False.elim (h3 hP)
            · exact rfl
          · intro hF
            rw [hF]
            exact ⟨Or.inr rfl, h4⟩
        rw [heq, Finset.card_singleton]
      have hShcard : ((sharedFaces M e).filter P).card = 1 := by omega
      have haσ : a ∈ edgesOf σ := edge_of_shared_pos (by omega)
      have hσcard : (σ.filter P).card = 2 := by
        simpa only [edgeDeg, P] using hσ.closed a haσ
      rw [hτcard, hOldCard, hσcard, hShcard, hEcard]
    · have hEcard : ((exposedFaces M e).filter P).card = 0 := by
        rw [hexp]
        have heq : ({f₃, f₄} : Finset (Finset V)).filter P = ∅ := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact False.elim (h3 hP)
            · exact False.elim (h4 hP)
          · intro hF
            cases hF
        rw [heq, Finset.card_empty]
      have hShcard : ((sharedFaces M e).filter P).card = 2 := by omega
      have haσ : a ∈ edgesOf σ := edge_of_shared_pos (by omega)
      have hσcard : (σ.filter P).card = 2 := by
        simpa only [edgeDeg, P] using hσ.closed a haσ
      have hdeg0 : edgeDeg ((σ \ sharedFaces M e) ∪ exposedFaces M e) a = 0 := by
        rw [hτcard, hOldCard, hσcard, hShcard, hEcard]
      have hτpos : 0 < edgeDeg ((σ \ sharedFaces M e) ∪ exposedFaces M e) a := by
        rw [edgeDeg]
        obtain ⟨F, hFτ, hFa, _⟩ := mem_edgesOf.mp haτ
        exact Finset.card_pos.mpr ⟨F, Finset.mem_filter.mpr ⟨hFτ, hFa⟩⟩
      omega

theorem flipBoundary_closed_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ∀ a ∈ edgesOf ((σ \ sharedFaces M e) ∪ exposedFaces M e),
      edgeDeg ((σ \ sharedFaces M e) ∪ exposedFaces M e) a = 2 := by
  classical
  intro a ha
  set τ : Finset (Finset V) := (σ \ sharedFaces M e) ∪ exposedFaces M e with hτdef
  by_cases hae : a ⊆ e
  · exact flipBoundary_closed_edge_in_tet_of_eligible hσ hU hS he hexp hf hNoFlip ha hae
  · have hNoTet : ∀ f ∈ tetFaces e, ¬ a ⊆ f := by
      intro f hf haf
      have hfe : f ⊆ e := (Finset.mem_powersetCard.mp hf).1
      exact hae (haf.trans hfe)
    have hfilter : τ.filter (fun f => a ⊆ f) = σ.filter (fun f => a ⊆ f) := by
      ext f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hfτ, haf⟩
        rw [hτdef, Finset.mem_union, Finset.mem_sdiff] at hfτ
        rcases hfτ with h | h
        · exact ⟨h.1, haf⟩
        · exact (hNoTet f (exposedFaces_subset_tetFaces M e h) haf).elim
      · rintro ⟨hfσ, haf⟩
        refine ⟨?_, haf⟩
        rw [hτdef, Finset.mem_union, Finset.mem_sdiff]
        left
        refine ⟨hfσ, ?_⟩
        intro hfs
        exact hNoTet f (sharedFaces_subset_tetFaces M e hfs) haf
    have haσ : a ∈ edgesOf σ := by
      rw [mem_edgesOf] at ha ⊢
      obtain ⟨f, hfτ, haf, hac⟩ := ha
      rw [hτdef, Finset.mem_union, Finset.mem_sdiff] at hfτ
      rcases hfτ with h | h
      · exact ⟨f, h.1, haf, hac⟩
      · exact (hNoTet f (exposedFaces_subset_tetFaces M e h) haf).elim
    rw [edgeDeg, hfilter]
    exact hσ.closed a haσ

theorem tetFaces_pair_union_eq {e F G : Finset V} (he : e.card = 4) (hF : F ∈ tetFaces e) (hG : G ∈ tetFaces e)
    (hFG : F ≠ G) :
    F ∪ G = e := by
  rw [Finset.ext_iff]
  intro x
  constructor
  · intro hx
    exact (Finset.mem_union.mp hx).elim (fun hxF => (by
      have hFs : F ⊆ e := by
        rw [tetFaces, mem_powersetCard] at hF
        exact hF.1
      exact hFs hxF)) (fun hxG => (by
      have hGs : G ⊆ e := by
        rw [tetFaces, mem_powersetCard] at hG
        exact hG.1
      exact hGs hxG))
  · intro hx
    by_contra hxnot
    have hxF : x ∉ F := by
      intro h
      exact hxnot (Finset.mem_union.mpr (Or.inl h))
    have hxG : x ∉ G := by
      intro h
      exact hxnot (Finset.mem_union.mpr (Or.inr h))
    have hFs : F ⊆ e := by
      rw [tetFaces, mem_powersetCard] at hF
      exact hF.1
    have hGs : G ⊆ e := by
      rw [tetFaces, mem_powersetCard] at hG
      exact hG.1
    have hFc : F.card = 3 := by
      rw [tetFaces, mem_powersetCard] at hF
      exact hF.2
    have hGc : G.card = 3 := by
      rw [tetFaces, mem_powersetCard] at hG
      exact hG.2
    have hFerase : F ⊆ e.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by
        intro hyx
        subst hyx
        exact hxF hy, hFs hy⟩
    have hGerase : G ⊆ e.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by
        intro hyx
        subst hyx
        exact hxG hy, hGs hy⟩
    have herasecard : (e.erase x).card = 3 := by
      rw [Finset.card_erase_of_mem hx, he]
    have hFeq : F = e.erase x := by
      apply Finset.eq_of_subset_of_card_le hFerase
      rw [hFc, herasecard]
    have hGeq : G = e.erase x := by
      apply Finset.eq_of_subset_of_card_le hGerase
      rw [hGc, herasecard]
    exact hFG (hFeq.trans hGeq.symm)

theorem tetFaces_pair_inter_card_eq_two {e F G : Finset V} (he : e.card = 4) (hF : F ∈ tetFaces e) (hG : G ∈ tetFaces e)
    (hFG : F ≠ G) :
    (F ∩ G).card = 2 := by
  have hU : (F ∪ G).card = 4 := by
    rw [tetFaces_pair_union_eq he hF hG hFG]
    exact he
  have hFmem : F ⊆ e ∧ F.card = 3 := by
    simpa [tetFaces] using hF
  have hGmem : G ⊆ e ∧ G.card = 3 := by
    simpa [tetFaces] using hG
  have hFc : F.card = 3 := hFmem.2
  have hGc : G.card = 3 := hGmem.2
  have hcard := card_union_add_card_inter F G
  omega

theorem flipBoundary_linkConn_newDiag_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) {v : V} (hvnew : v ∈ f₃ ∩ f₄) :
    ConnOn (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v)
      (linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v) := by
  classical
  have hf3exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, true_or]
  have hf4exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, or_true]
  have hf3tet : f₃ ∈ tetFaces e := ((mem_exposedFaces_iff_tetFace_not_sigma hU) f₃).mp hf3exp |>.1
  have hf4tet : f₄ ∈ tetFaces e := ((mem_exposedFaces_iff_tetFace_not_sigma hU) f₄).mp hf4exp |>.1
  have hf3info := Finset.mem_powersetCard.mp hf3tet
  have hf4info := Finset.mem_powersetCard.mp hf4tet
  have hf3sub : f₃ ⊆ e := hf3info.1
  have hf4sub : f₄ ⊆ e := hf4info.1
  have hf3card : f₃.card = 3 := hf3info.2
  have hf4card : f₄.card = 3 := hf4info.2
  have hfg_union : f₃ ∪ f₄ = e := tetFaces_pair_union_eq he.1 hf3tet hf4tet hf
  have hint_card : (f₃ ∩ f₄).card = 2 := tetFaces_pair_inter_card_eq_two he.1 hf3tet hf4tet hf
  have herase_card : ((f₃ ∩ f₄).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvnew, hint_card]
  obtain ⟨w, hwpair⟩ := Finset.card_eq_one.mp herase_card
  have hw_erase : w ∈ (f₃ ∩ f₄).erase v := by
    rw [hwpair]
    exact Finset.mem_singleton_self w
  have hwnew : w ∈ f₃ ∩ f₄ := Finset.mem_of_mem_erase hw_erase
  have hwv : w ≠ v := Finset.ne_of_mem_erase hw_erase
  have hvf3 : v ∈ f₃ := (Finset.mem_inter.mp hvnew).1
  have hvf4 : v ∈ f₄ := (Finset.mem_inter.mp hvnew).2
  have hwf3 : w ∈ f₃ := (Finset.mem_inter.mp hwnew).1
  have hwf4 : w ∈ f₄ := (Finset.mem_inter.mp hwnew).2
  have hve : v ∈ e := hf3sub hvf3
  have hwe : w ∈ e := hf3sub hwf3
  have hdiag_eq : f₃ ∩ f₄ = {v, w} := by
    ext z
    constructor
    · intro hz
      by_cases hzv : z = v
      · rw [hzv]
        simp only [mem_insert, mem_singleton, true_or]
      · have hz_erase : z ∈ (f₃ ∩ f₄).erase v := Finset.mem_erase.mpr ⟨hzv, hz⟩
        rw [hwpair] at hz_erase
        rw [Finset.mem_singleton] at hz_erase
        rw [hz_erase]
        simp only [mem_insert, mem_singleton, or_true]
    · intro hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hvnew
      · exact hwnew
  have hno_vw_face : ∀ F, F ∈ σ → v ∈ F → w ∈ F → False := by
    intro F hF hvF hwF
    have hedge : ({v, w} : Finset V) ∈ edgesOf σ := by
      refine mem_edgesOf.mpr ⟨F, hF, ?_, Finset.card_pair (Ne.symm hwv)⟩
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hvF
      · exact hwF
    exact hNoFlip (by
      unfold FlipEdgePresent
      rw [hdiag_eq]
      exact hedge)
  have hS_tet : e.erase w ∈ tetFaces e := erase_mem_tetFaces he.1 hwe
  have hS_ne_f3 : e.erase w ≠ f₃ := by
    intro hEq
    have : w ∈ e.erase w := by
      rw [hEq]
      exact hwf3
    exact Finset.notMem_erase w e this
  have hS_ne_f4 : e.erase w ≠ f₄ := by
    intro hEq
    have : w ∈ e.erase w := by
      rw [hEq]
      exact hwf4
    exact Finset.notMem_erase w e this
  have hS_not_exp : e.erase w ∉ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton]
    intro hmem
    rcases hmem with hEq | hEq
    · exact hS_ne_f3 hEq
    · exact hS_ne_f4 hEq
  have hSσ : e.erase w ∈ σ := by
    by_contra hnot
    exact hS_not_exp (((mem_exposedFaces_iff_tetFace_not_sigma hU) (e.erase w)).mpr ⟨hS_tet, hnot⟩)
  have hvS : v ∈ e.erase w := Finset.mem_erase.mpr ⟨Ne.symm hwv, hve⟩
  have hcases : ∀ z, z ∈ linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v →
      z = w ∨ z ∈ linkVerts σ v := by
    intro z hz
    obtain ⟨hzv, F, hFτ, hvF, hzF⟩ := mem_linkVerts.mp hz
    rw [Finset.mem_union] at hFτ
    rcases hFτ with hFsd | hFexp
    · right
      obtain ⟨hFσ, _⟩ := Finset.mem_sdiff.mp hFsd
      exact mem_linkVerts.mpr ⟨hzv, F, hFσ, hvF, hzF⟩
    · rw [hexp] at hFexp
      simp only [mem_insert, mem_singleton] at hFexp
      by_cases hzw : z = w
      · exact Or.inl hzw
      · right
        have hze : z ∈ e := by
          rcases hFexp with rfl | rfl
          · exact hf3sub hzF
          · exact hf4sub hzF
        have hzS : z ∈ e.erase w := Finset.mem_erase.mpr ⟨hzw, hze⟩
        exact mem_linkVerts.mpr ⟨hzv, e.erase w, hSσ, hvS, hzS⟩
  have hw_in_f3_erase_v : w ∈ f₃.erase v := Finset.mem_erase.mpr ⟨hwv, hwf3⟩
  have hanchor_card : ((f₃.erase v).erase w).card = 1 := by
    rw [Finset.card_erase_of_mem hw_in_f3_erase_v, Finset.card_erase_of_mem hvf3, hf3card]
  obtain ⟨a, hapair⟩ := Finset.card_eq_one.mp hanchor_card
  have ha_erase : a ∈ (f₃.erase v).erase w := by
    rw [hapair]
    exact Finset.mem_singleton_self a
  have ha_f3_erase_v : a ∈ f₃.erase v := Finset.mem_of_mem_erase ha_erase
  have haf3 : a ∈ f₃ := Finset.mem_of_mem_erase ha_f3_erase_v
  have haw_ne : a ≠ w := Finset.ne_of_mem_erase ha_erase
  have hav : a ≠ v := Finset.ne_of_mem_erase ha_f3_erase_v
  have hae : a ∈ e := hf3sub haf3
  have haS : a ∈ e.erase w := Finset.mem_erase.mpr ⟨haw_ne, hae⟩
  have haσ : a ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hav, e.erase w, hSσ, hvS, haS⟩
  have hface_aw : ({v, a, w} : Finset V) = f₃ := by
    have hsub : ({v, a, w} : Finset V) ⊆ f₃ := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hvf3
      · exact haf3
      · exact hwf3
    have hcardvaw : ({v, a, w} : Finset V).card = 3 :=
      Finset.card_eq_three.mpr ⟨v, a, w, Ne.symm hav, Ne.symm hwv, haw_ne, rfl⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardvaw, hf3card])
  have haw : (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj a w := by
    refine ⟨haw_ne, ?_⟩
    rw [hface_aw]
    exact Finset.mem_union.mpr (Or.inr hf3exp)
  have hvσ : v ∈ vertsOf σ := by
    obtain ⟨_, F, hFσ, hvF, _⟩ := mem_linkVerts.mp haσ
    exact mem_vertsOf.mpr ⟨F, hFσ, hvF⟩
  have adj_to_w : ∀ {z : V}, z ≠ v → z ≠ w → z ∈ e →
      (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj z w := by
    intro z hzv hzw hze
    have hzfw : z ∈ f₃ ∨ z ∈ f₄ := by
      have hzunion : z ∈ f₃ ∪ f₄ := by
        rw [hfg_union]
        exact hze
      exact Finset.mem_union.mp hzunion
    rcases hzfw with hzf3 | hzf4
    · refine ⟨hzw, ?_⟩
      have hface : ({v, z, w} : Finset V) = f₃ := by
        have hsub : ({v, z, w} : Finset V) ⊆ f₃ := by
          intro u hu
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact hvf3
          · exact hzf3
          · exact hwf3
        have hcardvzw : ({v, z, w} : Finset V).card = 3 :=
          Finset.card_eq_three.mpr ⟨v, z, w, Ne.symm hzv, Ne.symm hwv, hzw, rfl⟩
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardvzw, hf3card])
      rw [hface]
      exact Finset.mem_union.mpr (Or.inr hf3exp)
    · refine ⟨hzw, ?_⟩
      have hface : ({v, z, w} : Finset V) = f₄ := by
        have hsub : ({v, z, w} : Finset V) ⊆ f₄ := by
          intro u hu
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact hvf4
          · exact hzf4
          · exact hwf4
        have hcardvzw : ({v, z, w} : Finset V).card = 3 :=
          Finset.card_eq_three.mpr ⟨v, z, w, Ne.symm hzv, Ne.symm hwv, hzw, rfl⟩
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardvzw, hf4card])
      rw [hface]
      exact Finset.mem_union.mpr (Or.inr hf4exp)
  have hstep : ∀ {x y : V}, (linkGraph σ v).Adj x y →
      (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Reachable x y := by
    intro x y hxyσ
    obtain ⟨hxy_ne, hFσ⟩ := hxyσ
    by_cases hFshared : ({v, x, y} : Finset V) ∈ sharedFaces M e
    · have hne_v := face_two_ne hσ hFσ
      have hxv : x ≠ v := hne_v.1
      have hyv : y ≠ v := hne_v.2
      have hxw : x ≠ w := by
        intro hxw
        exact hno_vw_face {v, x, y} hFσ (by simp) (by rw [← hxw]; simp)
      have hyw : y ≠ w := by
        intro hyw
        exact hno_vw_face {v, x, y} hFσ (by simp) (by rw [← hyw]; simp)
      have hFtet : ({v, x, y} : Finset V) ∈ tetFaces e := by
        have hshared_eq := sharedFaces_eq_tetFaces_inter_sigma (M := M) (σ := σ) (e := e) hU
        rw [hshared_eq] at hFshared
        exact (Finset.mem_inter.mp hFshared).1
      have hFsub : ({v, x, y} : Finset V) ⊆ e := (Finset.mem_powersetCard.mp hFtet).1
      have hxe : x ∈ e := hFsub (by simp)
      have hye : y ∈ e := hFsub (by simp)
      exact (adj_to_w hxv hxw hxe).reachable.trans (adj_to_w hyv hyw hye).symm.reachable
    · exact (show (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj x y from
        ⟨hxy_ne, Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hFσ, hFshared⟩))⟩).reachable
  have lift_walk : ∀ {x y : V}, (linkGraph σ v).Walk x y →
      (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Reachable x y := by
    intro x y p
    induction p with
    | nil => exact ⟨SimpleGraph.Walk.nil⟩
    | cons hxy _ ih => exact (hstep hxy).trans ih
  have reach_w : ∀ z, z ∈ linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v →
      (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Reachable z w := by
    intro z hz
    rcases hcases z hz with hzw | hzσ
    · rw [hzw]
    · obtain ⟨p⟩ := hσ.linkConn v hvσ z hzσ a haσ
      exact (lift_walk p).trans haw.reachable
  intro x hx y hy
  exact (reach_w x hx).trans (reach_w y hy).symm

theorem flipBoundary_oldDiag_link_local_data {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) {v : V} (hve : v ∈ e) (hvnotnew : v ∉ f₃ ∩ f₄) :
    ∃ w p q : V,
      v ∈ vertsOf σ ∧
      p ≠ q ∧
      linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v = (linkVerts σ v).erase w ∧
      (linkVerts σ v).filter (fun y => (linkGraph σ v).Adj w y) = {p, q} ∧
      (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj p q ∧
      (∀ {a b : V}, a ∈ (linkVerts σ v).erase w → b ∈ (linkVerts σ v).erase w →
        (linkGraph σ v).Adj a b → (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj a b) ∧
      (∀ {a b : V}, a ∈ linkVerts σ v → (linkGraph σ v).Adj a b → b ∈ linkVerts σ v) := by
  classical
  have ht4 : e.card = 4 := he.1
  have hf3exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, true_or]
  have hf4exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, or_true]
  have hf3tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf3exp
  have hf4tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf4exp
  have hcd2 : (f₃ ∩ f₄).card = 2 := tetFaces_pair_inter_card_eq_two ht4 hf3tet hf4tet hf
  obtain ⟨p, q, hpq, hcd_eq⟩ := Finset.card_eq_two.mp hcd2
  have hcd_sub_e : f₃ ∩ f₄ ⊆ e := by
    intro x hx
    exact (Finset.mem_powersetCard.mp hf3tet).1 (Finset.mem_of_mem_inter_left hx)
  have hmain : ∀ w : V, v ≠ w → e \ (f₃ ∩ f₄) = ({v, w} : Finset V) →
      ∃ w p q : V,
        v ∈ vertsOf σ ∧
        p ≠ q ∧
        linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v = (linkVerts σ v).erase w ∧
        (linkVerts σ v).filter (fun y => (linkGraph σ v).Adj w y) = {p, q} ∧
        (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj p q ∧
        (∀ {a b : V}, a ∈ (linkVerts σ v).erase w → b ∈ (linkVerts σ v).erase w →
          (linkGraph σ v).Adj a b → (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v).Adj a b) ∧
        (∀ {a b : V}, a ∈ linkVerts σ v → (linkGraph σ v).Adj a b → b ∈ linkVerts σ v) := by
    intro w hvw hdiff_vw
    have he_eq : e = ({v, w} : Finset V) ∪ {p, q} := by
      rw [← hdiff_vw, ← hcd_eq]
      exact (Finset.sdiff_union_of_subset hcd_sub_e).symm
    have hv_not_cd : v ∉ f₃ ∩ f₄ := hvnotnew
    have hvp : v ≠ p := by
      intro h
      apply hv_not_cd
      rw [hcd_eq]
      simp [h]
    have hvq : v ≠ q := by
      intro h
      apply hv_not_cd
      rw [hcd_eq]
      simp [h]
    have hwp : w ≠ p := by
      intro h
      have hwmem : w ∈ e \ (f₃ ∩ f₄) := by rw [hdiff_vw]; simp [hvw]
      exact (Finset.mem_sdiff.mp hwmem).2 (by rw [h, hcd_eq]; simp)
    have hwq : w ≠ q := by
      intro h
      have hwmem : w ∈ e \ (f₃ ∩ f₄) := by rw [hdiff_vw]; simp [hvw]
      exact (Finset.mem_sdiff.mp hwmem).2 (by rw [h, hcd_eq]; simp)
    have hp_cd : p ∈ f₃ ∩ f₄ := by rw [hcd_eq]; simp
    have hq_cd : q ∈ f₃ ∩ f₄ := by rw [hcd_eq]; simp
    have hp_f3 : p ∈ f₃ := (Finset.mem_inter.mp hp_cd).1
    have hp_f4 : p ∈ f₄ := (Finset.mem_inter.mp hp_cd).2
    have hq_f3 : q ∈ f₃ := (Finset.mem_inter.mp hq_cd).1
    have hq_f4 : q ∈ f₄ := (Finset.mem_inter.mp hq_cd).2
    have hpq_sub_vpq : ({p, q} : Finset V) ⊆ ({v, p, q} : Finset V) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    have hpq_sub_wpq : ({p, q} : Finset V) ⊆ ({w, p, q} : Finset V) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    have hvw_sub_vwp : ({v, w} : Finset V) ⊆ ({v, w, p} : Finset V) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    have hvw_sub_vwq : ({v, w} : Finset V) ⊆ ({v, w, q} : Finset V) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    have hvpq_tet : ({v, p, q} : Finset V) ∈ tetFaces e := by
      rw [tetFaces, Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [he_eq]
        simp only [mem_union, mem_insert, mem_singleton]
        simp only [mem_insert, mem_singleton] at hx
        tauto
      · exact Finset.card_eq_three.mpr ⟨v, p, q, hvp, hvq, hpq, rfl⟩
    have hwpq_tet : ({w, p, q} : Finset V) ∈ tetFaces e := by
      rw [tetFaces, Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [he_eq]
        simp only [mem_union, mem_insert, mem_singleton]
        simp only [mem_insert, mem_singleton] at hx
        tauto
      · exact Finset.card_eq_three.mpr ⟨w, p, q, hwp, hwq, hpq, rfl⟩
    have hvwp_tet : ({v, w, p} : Finset V) ∈ tetFaces e := by
      rw [tetFaces, Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [he_eq]
        simp only [mem_union, mem_insert, mem_singleton]
        simp only [mem_insert, mem_singleton] at hx
        tauto
      · exact Finset.card_eq_three.mpr ⟨v, w, p, hvw, hvp, hwp, rfl⟩
    have hvwq_tet : ({v, w, q} : Finset V) ∈ tetFaces e := by
      rw [tetFaces, Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [he_eq]
        simp only [mem_union, mem_insert, mem_singleton]
        simp only [mem_insert, mem_singleton] at hx
        tauto
      · exact Finset.card_eq_three.mpr ⟨v, w, q, hvw, hvq, hwq, rfl⟩
    have hNoEdge : f₃ ∩ f₄ ∉ edgesOf σ := by
      exact hNoFlip
    have hvpq_notσ : ({v, p, q} : Finset V) ∉ σ := by
      intro hface
      apply hNoEdge
      rw [hcd_eq]
      exact mem_edgesOf.mpr ⟨{v, p, q}, hface, hpq_sub_vpq, by rw [Finset.card_pair hpq]⟩
    have hwpq_notσ : ({w, p, q} : Finset V) ∉ σ := by
      intro hface
      apply hNoEdge
      rw [hcd_eq]
      exact mem_edgesOf.mpr ⟨{w, p, q}, hface, hpq_sub_wpq, by rw [Finset.card_pair hpq]⟩
    have hvpq_exp : ({v, p, q} : Finset V) ∈ exposedFaces M e := by
      rw [mem_exposedFaces_iff_tetFace_not_sigma hU]
      exact ⟨hvpq_tet, hvpq_notσ⟩
    have hwpq_exp : ({w, p, q} : Finset V) ∈ exposedFaces M e := by
      rw [mem_exposedFaces_iff_tetFace_not_sigma hU]
      exact ⟨hwpq_tet, hwpq_notσ⟩
    have hvwp_not_exp : ({v, w, p} : Finset V) ∉ exposedFaces M e := by
      rw [hexp]
      intro hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with hEq | hEq
      · have hqmem : q ∈ ({v, w, p} : Finset V) := by
          rw [hEq]
          exact hq_f3
        simp only [mem_insert, mem_singleton] at hqmem
        rcases hqmem with hqv | hqw | hqp
        · exact hvq hqv.symm
        · exact hwq hqw.symm
        · exact hpq hqp.symm
      · have hqmem : q ∈ ({v, w, p} : Finset V) := by
          rw [hEq]
          exact hq_f4
        simp only [mem_insert, mem_singleton] at hqmem
        rcases hqmem with hqv | hqw | hqp
        · exact hvq hqv.symm
        · exact hwq hqw.symm
        · exact hpq hqp.symm
    have hvwq_not_exp : ({v, w, q} : Finset V) ∉ exposedFaces M e := by
      rw [hexp]
      intro hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with hEq | hEq
      · have hpmem : p ∈ ({v, w, q} : Finset V) := by
          rw [hEq]
          exact hp_f3
        simp only [mem_insert, mem_singleton] at hpmem
        rcases hpmem with hpv | hpw | hpqeq
        · exact hvp hpv.symm
        · exact hwp hpw.symm
        · exact hpq hpqeq
      · have hpmem : p ∈ ({v, w, q} : Finset V) := by
          rw [hEq]
          exact hp_f4
        simp only [mem_insert, mem_singleton] at hpmem
        rcases hpmem with hpv | hpw | hpqeq
        · exact hvp hpv.symm
        · exact hwp hpw.symm
        · exact hpq hpqeq
    have hvwp_sigma : ({v, w, p} : Finset V) ∈ σ := by
      by_contra hnot
      exact hvwp_not_exp ((mem_exposedFaces_iff_tetFace_not_sigma hU _).mpr ⟨hvwp_tet, hnot⟩)
    have hvwq_sigma : ({v, w, q} : Finset V) ∈ σ := by
      by_contra hnot
      exact hvwq_not_exp ((mem_exposedFaces_iff_tetFace_not_sigma hU _).mpr ⟨hvwq_tet, hnot⟩)
    have hvwp_shared : ({v, w, p} : Finset V) ∈ sharedFaces M e := by
      rw [sharedFaces_eq_tetFaces_inter_sigma hU]
      exact Finset.mem_inter.mpr ⟨hvwp_tet, hvwp_sigma⟩
    have hvwq_shared : ({v, w, q} : Finset V) ∈ sharedFaces M e := by
      rw [sharedFaces_eq_tetFaces_inter_sigma hU]
      exact Finset.mem_inter.mpr ⟨hvwq_tet, hvwq_sigma⟩
    have hvwp_ne_hvwq : ({v, w, p} : Finset V) ≠ ({v, w, q} : Finset V) := by
      intro hEq
      have hqmem : q ∈ ({v, w, p} : Finset V) := by rw [hEq]; simp
      simp only [mem_insert, mem_singleton] at hqmem
      rcases hqmem with hqv | hqw | hqp
      · exact hvq hqv.symm
      · exact hwq hqw.symm
      · exact hpq hqp.symm
    have holdPair_sub_shared : ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) ⊆ sharedFaces M e := by
      intro F hF
      simp only [mem_insert, mem_singleton] at hF
      rcases hF with rfl | rfl
      · exact hvwp_shared
      · exact hvwq_shared
    have hshared_eq_oldPair : sharedFaces M e = ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) := by
      exact (Finset.eq_of_subset_of_card_le holdPair_sub_shared (by rw [he.2.2.1, Finset.card_pair hvwp_ne_hvwq])).symm
    have hnew_ne : ({v, p, q} : Finset V) ≠ ({w, p, q} : Finset V) := by
      intro hEq
      have vmem : v ∈ ({w, p, q} : Finset V) := by rw [← hEq]; simp
      simp only [mem_insert, mem_singleton] at vmem
      rcases vmem with hvw' | hvp' | hvq'
      · exact hvw hvw'
      · exact hvp hvp'
      · exact hvq hvq'
    have hnewPair_sub_exp : ({({v, p, q} : Finset V), ({w, p, q} : Finset V)} : Finset (Finset V)) ⊆ exposedFaces M e := by
      intro F hF
      simp only [mem_insert, mem_singleton] at hF
      rcases hF with rfl | rfl
      · exact hvpq_exp
      · exact hwpq_exp
    have hexposed_eq_newPair : exposedFaces M e = ({({v, p, q} : Finset V), ({w, p, q} : Finset V)} : Finset (Finset V)) := by
      exact (Finset.eq_of_subset_of_card_le hnewPair_sub_exp (by rw [exposedFaces_card_of_eligible he, Finset.card_pair hnew_ne])).symm
    have hedge_vw : ({v, w} : Finset V) ∈ edgesOf σ := by
      exact mem_edgesOf.mpr ⟨{v, w, p}, hvwp_sigma, hvw_sub_vwp, Finset.card_pair hvw⟩
    have hfilter_vw_card : (σ.filter (fun F => ({v, w} : Finset V) ⊆ F)).card = 2 := by
      exact hσ.closed {v, w} hedge_vw
    have holdPair_sub_filter : ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) ⊆ σ.filter (fun F => ({v, w} : Finset V) ⊆ F) := by
      intro F hF
      simp only [mem_insert, mem_singleton] at hF
      rcases hF with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hvwp_sigma, hvw_sub_vwp⟩
      · exact Finset.mem_filter.mpr ⟨hvwq_sigma, hvw_sub_vwq⟩
    have hfilter_vw_eq : σ.filter (fun F => ({v, w} : Finset V) ⊆ F) = ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) := by
      exact (Finset.eq_of_subset_of_card_le holdPair_sub_filter (by rw [hfilter_vw_card, Finset.card_pair hvwp_ne_hvwq])).symm
    have hface_vw_shared : ∀ {F : Finset V}, F ∈ σ → v ∈ F → w ∈ F → F ∈ sharedFaces M e := by
      intro F hFσ hvF hwF
      have hsub : ({v, w} : Finset V) ⊆ F := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hvF
        · exact hwF
      have hFfilter : F ∈ σ.filter (fun F => ({v, w} : Finset V) ⊆ F) := Finset.mem_filter.mpr ⟨hFσ, hsub⟩
      have hFold : F ∈ ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) := by
        rw [← hfilter_vw_eq]
        exact hFfilter
      rw [hshared_eq_oldPair]
      exact hFold
    have hvσ : v ∈ vertsOf σ := mem_vertsOf.mpr ⟨{v, w, p}, hvwp_sigma, by simp⟩
    have hpL : p ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hvp.symm, {v, w, p}, hvwp_sigma, by simp, by simp⟩
    have hqL : q ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hvq.symm, {v, w, q}, hvwq_sigma, by simp, by simp⟩
    have hwL : w ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hvw.symm, {v, w, p}, hvwp_sigma, by simp, by simp⟩
    have hneighbors : (linkVerts σ v).filter (fun y => (linkGraph σ v).Adj w y) = ({p, q} : Finset V) := by
      have hcard := link_two_regular hσ hwL
      have hsub : ({p, q} : Finset V) ⊆ (linkVerts σ v).filter (fun y => (linkGraph σ v).Adj w y) := by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hpL, ⟨hwp, hvwp_sigma⟩⟩
        · exact Finset.mem_filter.mpr ⟨hqL, ⟨hwq, hvwq_sigma⟩⟩
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hpq])).symm
    refine ⟨w, p, q, hvσ, hpq, ?_, hneighbors, ?_, ?_, ?_⟩
    · ext y
      constructor
      · intro hy
        obtain ⟨hyv, F, hFτ, hvF, hyF⟩ := mem_linkVerts.mp hy
        rcases Finset.mem_union.mp hFτ with hFold | hFexp
        · have hFσ : F ∈ σ := (Finset.mem_sdiff.mp hFold).1
          have hFnot : F ∉ sharedFaces M e := (Finset.mem_sdiff.mp hFold).2
          have hyw : y ≠ w := by
            intro hyw
            have hwF : w ∈ F := hyw ▸ hyF
            exact hFnot (hface_vw_shared hFσ hvF hwF)
          exact Finset.mem_erase.mpr ⟨hyw, mem_linkVerts.mpr ⟨hyv, F, hFσ, hvF, hyF⟩⟩
        · have hFcase : F = ({v, p, q} : Finset V) ∨ F = ({w, p, q} : Finset V) := by
            have htmp := hFexp
            rw [hexposed_eq_newPair] at htmp
            simp only [mem_insert, mem_singleton] at htmp
            exact htmp
          rcases hFcase with hFvpq | hFwpq
          · have hycase : y = v ∨ y = p ∨ y = q := by
              rw [hFvpq] at hyF
              simp only [mem_insert, mem_singleton] at hyF
              exact hyF
            rcases hycase with rfl | rfl | rfl
            · exact False.elim (hyv rfl)
            · exact Finset.mem_erase.mpr ⟨hwp.symm, hpL⟩
            · exact Finset.mem_erase.mpr ⟨hwq.symm, hqL⟩
          · have hvcase : v = w ∨ v = p ∨ v = q := by
              rw [hFwpq] at hvF
              simp only [mem_insert, mem_singleton] at hvF
              exact hvF
            rcases hvcase with hvw' | hvp' | hvq'
            · exact False.elim (hvw hvw')
            · exact False.elim (hvp hvp')
            · exact False.elim (hvq hvq')
      · intro hy
        have hyw : y ≠ w := (Finset.mem_erase.mp hy).1
        have hyOld : y ∈ linkVerts σ v := (Finset.mem_erase.mp hy).2
        have hyv : y ≠ v := (mem_linkVerts.mp hyOld).1
        by_cases hyp : y = p
        · subst y
          exact mem_linkVerts.mpr ⟨hvp.symm, {v, p, q}, Finset.mem_union.mpr (Or.inr hvpq_exp), by simp, by simp⟩
        · by_cases hyq : y = q
          · subst y
            exact mem_linkVerts.mpr ⟨hvq.symm, {v, p, q}, Finset.mem_union.mpr (Or.inr hvpq_exp), by simp, by simp⟩
          · obtain ⟨_, F, hFσ, hvF, hyF⟩ := mem_linkVerts.mp hyOld
            have hFnot : F ∉ sharedFaces M e := by
              intro hFsh
              have hFold : F ∈ ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) := by
                rw [← hshared_eq_oldPair]
                exact hFsh
              simp only [mem_insert, mem_singleton] at hFold
              rcases hFold with hEq | hEq
              · have hycase : y = v ∨ y = w ∨ y = p := by
                  rw [hEq] at hyF
                  simp only [mem_insert, mem_singleton] at hyF
                  exact hyF
                rcases hycase with hyv' | hyw' | hyp'
                · exact hyv hyv'
                · exact hyw hyw'
                · exact hyp hyp'
              · have hycase : y = v ∨ y = w ∨ y = q := by
                  rw [hEq] at hyF
                  simp only [mem_insert, mem_singleton] at hyF
                  exact hyF
                rcases hycase with hyv' | hyw' | hyq'
                · exact hyv hyv'
                · exact hyw hyw'
                · exact hyq hyq'
            exact mem_linkVerts.mpr ⟨hyv, F, Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hFσ, hFnot⟩)), hvF, hyF⟩
    · exact ⟨hpq, Finset.mem_union.mpr (Or.inr hvpq_exp)⟩
    · intro a b ha hb hadj
      have haE := Finset.mem_erase.mp ha
      have hbE := Finset.mem_erase.mp hb
      have haw : a ≠ w := haE.1
      have hbw : b ≠ w := hbE.1
      have hfaceσ : ({v, a, b} : Finset V) ∈ σ := hadj.2
      have hnot_shared : ({v, a, b} : Finset V) ∉ sharedFaces M e := by
        intro hsh
        have hFold : ({v, a, b} : Finset V) ∈ ({({v, w, p} : Finset V), ({v, w, q} : Finset V)} : Finset (Finset V)) := by
          rw [← hshared_eq_oldPair]
          exact hsh
        simp only [mem_insert, mem_singleton] at hFold
        rcases hFold with hEq | hEq
        · have hwcase : w = v ∨ w = a ∨ w = b := by
            have hwmem : w ∈ ({v, a, b} : Finset V) := by
              rw [hEq]
              simp [hvw]
            simp only [mem_insert, mem_singleton] at hwmem
            exact hwmem
          rcases hwcase with hwv | hwa | hwb
          · exact hvw hwv.symm
          · exact haw hwa.symm
          · exact hbw hwb.symm
        · have hwcase : w = v ∨ w = a ∨ w = b := by
            have hwmem : w ∈ ({v, a, b} : Finset V) := by
              rw [hEq]
              simp [hvw]
            simp only [mem_insert, mem_singleton] at hwmem
            exact hwmem
          rcases hwcase with hwv | hwa | hwb
          · exact hvw hwv.symm
          · exact haw hwa.symm
          · exact hbw hwb.symm
      exact ⟨hadj.1, Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hfaceσ, hnot_shared⟩))⟩
    · intro a b ha hab
      have hav : a ≠ v := (mem_linkVerts.mp ha).1
      have hface : ({v, a, b} : Finset V) ∈ σ := hab.2
      have hbv : b ≠ v := by
        intro hbv
        have hcard3 : ({v, a, b} : Finset V).card = 3 := hσ.pure _ hface
        rw [hbv] at hcard3
        simp only [Finset.insert_eq_of_mem, Finset.mem_insert, Finset.mem_singleton, true_or, or_true] at hcard3
        have hcard2 : ({a, v} : Finset V).card = 2 := Finset.card_pair hav
        rw [hcard2] at hcard3
        norm_num at hcard3
      exact mem_linkVerts.mpr ⟨hbv, {v, a, b}, hface, by simp, by simp⟩
  have hvcdiff : v ∈ e \ (f₃ ∩ f₄) := Finset.mem_sdiff.mpr ⟨hve, hvnotnew⟩
  have hdiffcard : (e \ (f₃ ∩ f₄)).card = 2 := by
    rw [Finset.card_sdiff_of_subset hcd_sub_e, ht4, hcd2]
  obtain ⟨x, y, hxy, hdiff_eq⟩ := Finset.card_eq_two.mp hdiffcard
  have hvxy : v = x ∨ v = y := by
    have hvmem : v ∈ ({x, y} : Finset V) := by
      rw [← hdiff_eq]
      exact hvcdiff
    simp only [mem_insert, mem_singleton] at hvmem
    exact hvmem
  cases hvxy with
  | inl hvx =>
      subst x
      exact hmain y hxy hdiff_eq
  | inr hvy =>
      subst y
      have hvx : v ≠ x := fun h => hxy h.symm
      have hdiff_vx : e \ (f₃ ∩ f₄) = ({v, x} : Finset V) := by
        rw [hdiff_eq, Finset.pair_comm]
      exact hmain x hvx hdiff_vx

theorem flipBoundary_linkConn_oldDiag_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) {v : V} (hve : v ∈ e) (hvnotnew : v ∉ f₃ ∩ f₄) :
    ConnOn (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v)
      (linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v) := by
  classical
  let τ : Finset (Finset V) := (σ \ sharedFaces M e) ∪ exposedFaces M e
  rcases flipBoundary_oldDiag_link_local_data (M := M) (σ := σ) (e := e) (f₃ := f₃) (f₄ := f₄)
      hσ hU hS he hexp hf hNoFlip hve hvnotnew with
    ⟨w, p, q, hvσ, hpq, hverts, hNbr, hHedge, hPres, hClosed⟩
  rw [hverts]
  exact connOn_erase_of_degree_two_bypass (G := linkGraph σ v) (H := linkGraph τ v)
    (S := linkVerts σ v) (x := w) (p := p) (q := q)
    (hσ.linkConn v hvσ) hpq hClosed hNbr hHedge hPres

theorem flipBoundary_linkConn_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ∀ v ∈ vertsOf ((σ \ sharedFaces M e) ∪ exposedFaces M e),
      ConnOn (linkGraph ((σ \ sharedFaces M e) ∪ exposedFaces M e) v)
        (linkVerts ((σ \ sharedFaces M e) ∪ exposedFaces M e) v) := by
  intro v hv
  by_cases hve : v ∈ e
  · by_cases hvnew : v ∈ f₃ ∩ f₄
    · exact flipBoundary_linkConn_newDiag_of_eligible hσ hU hS he hexp hf hNoFlip hvnew
    · exact flipBoundary_linkConn_oldDiag_of_eligible hσ hU hS he hexp hf hNoFlip hve hvnew
  · let σe : Finset (Finset V) := (σ \ sharedFaces M e) ∪ exposedFaces M e
    have hvσ : v ∈ vertsOf σ := by
      have hverts := flipBoundary_verts_eq hσ hU hS he hexp hf hNoFlip
      simpa only [hverts] using hv
    have hface : ∀ {s : Finset V}, v ∈ s → (s ∈ σe ↔ s ∈ σ) := by
      intro s hvs
      constructor
      · intro hs
        change s ∈ (σ \ sharedFaces M e) ∪ exposedFaces M e at hs
        rw [Finset.mem_union] at hs
        rcases hs with hs | hs
        · exact (Finset.mem_sdiff.mp hs).1
        · exfalso
          have hsTet : s ∈ tetFaces e := exposedFaces_subset_tetFaces M e hs
          have hsub : s ⊆ e := (Finset.mem_powersetCard.mp hsTet).1
          exact hve (hsub hvs)
      · intro hs
        have hnotShared : s ∉ sharedFaces M e := by
          intro hsh
          have hsTet : s ∈ tetFaces e := sharedFaces_subset_tetFaces M e hsh
          have hsub : s ⊆ e := (Finset.mem_powersetCard.mp hsTet).1
          exact hve (hsub hvs)
        change s ∈ (σ \ sharedFaces M e) ∪ exposedFaces M e
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hs, hnotShared⟩))
    have hG : linkGraph σe v = linkGraph σ v := by
      ext a b
      constructor
      · intro h
        exact ⟨h.1, (hface (by simp)).mp h.2⟩
      · intro h
        exact ⟨h.1, (hface (by simp)).mpr h.2⟩
    have hL : linkVerts σe v = linkVerts σ v := by
      ext x
      rw [mem_linkVerts, mem_linkVerts]
      constructor
      · rintro ⟨hxv, f, hf, hvf, hxf⟩
        exact ⟨hxv, f, (hface hvf).mp hf, hvf, hxf⟩
      · rintro ⟨hxv, f, hf, hvf, hxf⟩
        exact ⟨hxv, f, (hface hvf).mpr hf, hvf, hxf⟩
    change ConnOn (linkGraph σe v) (linkVerts σe v)
    rw [hG, hL]
    exact hσ.linkConn v hvσ

theorem three_mul_card_faces_of_pure_closed {τ : Finset (Finset V)}
    (hpure : ∀ f ∈ τ, f.card = 3)
    (hclosed : ∀ a ∈ edgesOf τ, edgeDeg τ a = 2) :
    3 * τ.card = 2 * (edgesOf τ).card := by
  classical
  have hfilter : ∀ f ∈ τ, (edgesOf τ).filter (fun e => e ⊆ f)
      = f.powersetCard 2 := by
    intro f hf
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨he, hef⟩
      exact ⟨hef, card_of_mem_edgesOf he⟩
    · rintro ⟨hef, hcard⟩
      exact ⟨mem_edgesOf.mpr ⟨f, hf, hef, hcard⟩, hef⟩
  have key : ∑ f ∈ τ, ((edgesOf τ).filter (fun e => e ⊆ f)).card
      = ∑ e ∈ edgesOf τ, (τ.filter (fun f => e ⊆ f)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hcongr : ∀ f ∈ τ, ((edgesOf τ).filter (fun e => e ⊆ f)).card = 3 := by
    intro f hf
    rw [hfilter f hf, Finset.card_powersetCard, hpure f hf]
    rfl
  have hcl : ∀ e ∈ edgesOf τ, (τ.filter (fun f => e ⊆ f)).card = 2 := by
    intro e he
    exact hclosed e he
  have hleft : ∑ f ∈ τ, ((edgesOf τ).filter (fun e => e ⊆ f)).card
      = 3 * τ.card := by
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
  have hright : ∑ e ∈ edgesOf τ, (τ.filter (fun f => e ⊆ f)).card
      = 2 * (edgesOf τ).card := by
    rw [Finset.sum_congr rfl hcl, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hleft, key, hright]

theorem flipBoundary_euler_of_eligible {M : Chain V} {σ : Finset (Finset V)} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    (vertsOf ((σ \ sharedFaces M e) ∪ exposedFaces M e)).card +
        ((σ \ sharedFaces M e) ∪ exposedFaces M e).card =
      (edgesOf ((σ \ sharedFaces M e) ∪ exposedFaces M e)).card + 2 := by
  classical
  let τ : Finset (Finset V) := (σ \ sharedFaces M e) ∪ exposedFaces M e
  have hcard : τ.card = σ.card := by
    dsimp [τ]
    exact flipBoundary_card_faces_eq hσ hU hS he hexp hf hNoFlip
  have hpure : ∀ f ∈ τ, f.card = 3 := by
    intro f hfτ
    dsimp [τ] at hfτ ⊢
    exact flipBoundary_pure_of_eligible hσ hU hS he hexp hf hNoFlip f hfτ
  have hclosed : ∀ a ∈ edgesOf τ, edgeDeg τ a = 2 := by
    intro a ha
    dsimp [τ] at ha ⊢
    exact flipBoundary_closed_of_eligible hσ hU hS he hexp hf hNoFlip a ha
  have hdoubleτ : 3 * τ.card = 2 * (edgesOf τ).card := by
    exact three_mul_card_faces_of_pure_closed hpure hclosed
  have hdoubleσ : 3 * σ.card = 2 * (edgesOf σ).card := by
    exact three_mul_card_faces hσ
  have hedge : (edgesOf τ).card = (edgesOf σ).card := by
    omega
  have hvert : (vertsOf τ).card = (vertsOf σ).card := by
    dsimp [τ]
    rw [flipBoundary_verts_eq hσ hU hS he hexp hf hNoFlip]
  have heulerσ : (vertsOf σ).card + σ.card = (edgesOf σ).card + 2 := by
    exact hσ.euler
  dsimp [τ] at hvert hedge hcard hdoubleτ
  rw [hvert, hcard, hedge]
  exact heulerσ


/-- **The bistellar 2-2 flip preserves the 2-sphere (case 1).** With the flipped edge
`f₃ ∩ f₄` absent from `σ`, removing an eligible tet leaves a boundary that is again a
combinatorial 2-sphere. -/
theorem isSphere2_flipBoundary_of_eligible {M : Chain V} {σ : Finset (Finset V)}
    {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    IsSphere2 ((σ \ sharedFaces M e) ∪ exposedFaces M e) := by
  refine ⟨?pure, ?closed, ?linkConn, ?conn, ?euler⟩
  · exact flipBoundary_pure_of_eligible hσ hU hS he hexp hf hNoFlip
  · exact flipBoundary_closed_of_eligible hσ hU hS he hexp hf hNoFlip
  · exact flipBoundary_linkConn_of_eligible hσ hU hS he hexp hf hNoFlip
  · exact flipBoundary_conn_of_eligible hσ hU hS he hexp hf hNoFlip
  · exact flipBoundary_euler_of_eligible hσ hU hS he hexp hf hNoFlip

end Taut
