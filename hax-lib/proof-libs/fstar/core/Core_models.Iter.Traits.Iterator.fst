module Core_models.Iter.Traits.Iterator
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Iterator as t_Iterator}

include Core_models.Bundle {f_Item as f_Item}

include Core_models.Bundle {f_next_pre as f_next_pre}

include Core_models.Bundle {f_next_post as f_next_post}

include Core_models.Bundle {f_next as f_next}

include Core_models.Bundle {t_IteratorMethods as t_IteratorMethods}

include Core_models.Bundle {f_fold_pre as f_fold_pre}

include Core_models.Bundle {f_fold_post as f_fold_post}

include Core_models.Bundle {f_fold as f_fold}

include Core_models.Bundle {f_enumerate_pre as f_enumerate_pre}

include Core_models.Bundle {f_enumerate_post as f_enumerate_post}

include Core_models.Bundle {f_enumerate as f_enumerate}

include Core_models.Bundle {f_step_by_pre as f_step_by_pre}

include Core_models.Bundle {f_step_by_post as f_step_by_post}

include Core_models.Bundle {f_step_by as f_step_by}

include Core_models.Bundle {f_map_pre as f_map_pre}

include Core_models.Bundle {f_map_post as f_map_post}

include Core_models.Bundle {f_map as f_map}

include Core_models.Bundle {f_all_pre as f_all_pre}

include Core_models.Bundle {f_all_post as f_all_post}

include Core_models.Bundle {f_all as f_all}

include Core_models.Bundle {f_take_pre as f_take_pre}

include Core_models.Bundle {f_take_post as f_take_post}

include Core_models.Bundle {f_take as f_take}

include Core_models.Bundle {f_flat_map_pre as f_flat_map_pre}

include Core_models.Bundle {f_flat_map_post as f_flat_map_post}

include Core_models.Bundle {f_flat_map as f_flat_map}

include Core_models.Bundle {f_flatten_pre as f_flatten_pre}

include Core_models.Bundle {f_flatten_post as f_flatten_post}

include Core_models.Bundle {f_flatten as f_flatten}

include Core_models.Bundle {f_zip_pre as f_zip_pre}

include Core_models.Bundle {f_zip_post as f_zip_post}

include Core_models.Bundle {f_zip as f_zip}

include Core_models.Bundle {f_filter_pre as f_filter_pre}

include Core_models.Bundle {f_filter_post as f_filter_post}

include Core_models.Bundle {f_filter as f_filter}

include Core_models.Bundle {f_chain_pre as f_chain_pre}

include Core_models.Bundle {f_chain_post as f_chain_post}

include Core_models.Bundle {f_chain as f_chain}

include Core_models.Bundle {f_skip_pre as f_skip_pre}

include Core_models.Bundle {f_skip_post as f_skip_post}

include Core_models.Bundle {f_skip as f_skip}

include Core_models.Bundle {f_any_pre as f_any_pre}

include Core_models.Bundle {f_any_post as f_any_post}

include Core_models.Bundle {f_any as f_any}

include Core_models.Bundle {f_find_pre as f_find_pre}

include Core_models.Bundle {f_find_post as f_find_post}

include Core_models.Bundle {f_find as f_find}

include Core_models.Bundle {f_find_map_pre as f_find_map_pre}

include Core_models.Bundle {f_find_map_post as f_find_map_post}

include Core_models.Bundle {f_find_map as f_find_map}

include Core_models.Bundle {f_position_pre as f_position_pre}

include Core_models.Bundle {f_position_post as f_position_post}

include Core_models.Bundle {f_position as f_position}

include Core_models.Bundle {f_count_pre as f_count_pre}

include Core_models.Bundle {f_count_post as f_count_post}

include Core_models.Bundle {f_count as f_count}

include Core_models.Bundle {f_nth_pre as f_nth_pre}

include Core_models.Bundle {f_nth_post as f_nth_post}

include Core_models.Bundle {f_nth as f_nth}

include Core_models.Bundle {f_last_pre as f_last_pre}

include Core_models.Bundle {f_last_post as f_last_post}

include Core_models.Bundle {f_last as f_last}

include Core_models.Bundle {f_for_each_pre as f_for_each_pre}

include Core_models.Bundle {f_for_each_post as f_for_each_post}

include Core_models.Bundle {f_for_each as f_for_each}

include Core_models.Bundle {f_reduce_pre as f_reduce_pre}

include Core_models.Bundle {f_reduce_post as f_reduce_post}

include Core_models.Bundle {f_reduce as f_reduce}

include Core_models.Bundle {f_min_pre as f_min_pre}

include Core_models.Bundle {f_min_post as f_min_post}

include Core_models.Bundle {f_min as f_min}

include Core_models.Bundle {f_max_pre as f_max_pre}

include Core_models.Bundle {f_max_post as f_max_post}

include Core_models.Bundle {f_max as f_max}

include Core_models.Bundle {f_collect_pre as f_collect_pre}

include Core_models.Bundle {f_collect_post as f_collect_post}

include Core_models.Bundle {f_collect as f_collect}

include Core_models.Bundle {f_rev_pre as f_rev_pre}

include Core_models.Bundle {f_rev_post as f_rev_post}

include Core_models.Bundle {f_rev as f_rev}

include Core_models.Bundle {f_rposition_pre as f_rposition_pre}

include Core_models.Bundle {f_rposition_post as f_rposition_post}

include Core_models.Bundle {f_rposition as f_rposition}

include Core_models.Bundle {f_advance_by_pre as f_advance_by_pre}

include Core_models.Bundle {f_advance_by_post as f_advance_by_post}

include Core_models.Bundle {f_advance_by as f_advance_by}

include Core_models.Bundle {f_cloned_pre as f_cloned_pre}

include Core_models.Bundle {f_cloned_post as f_cloned_post}

include Core_models.Bundle {f_cloned as f_cloned}

include Core_models.Bundle {f_copied_pre as f_copied_pre}

include Core_models.Bundle {f_copied_post as f_copied_post}

include Core_models.Bundle {f_copied as f_copied}

include Core_models.Bundle {f_inspect_pre as f_inspect_pre}

include Core_models.Bundle {f_inspect_post as f_inspect_post}

include Core_models.Bundle {f_inspect as f_inspect}

include Core_models.Bundle {f_filter_map_pre as f_filter_map_pre}

include Core_models.Bundle {f_filter_map_post as f_filter_map_post}

include Core_models.Bundle {f_filter_map as f_filter_map}

include Core_models.Bundle {f_map_while_pre as f_map_while_pre}

include Core_models.Bundle {f_map_while_post as f_map_while_post}

include Core_models.Bundle {f_map_while as f_map_while}

include Core_models.Bundle {f_skip_while_pre as f_skip_while_pre}

include Core_models.Bundle {f_skip_while_post as f_skip_while_post}

include Core_models.Bundle {f_skip_while as f_skip_while}

include Core_models.Bundle {f_take_while_pre as f_take_while_pre}

include Core_models.Bundle {f_take_while_post as f_take_while_post}

include Core_models.Bundle {f_take_while as f_take_while}

include Core_models.Bundle {f_fuse_pre as f_fuse_pre}

include Core_models.Bundle {f_fuse_post as f_fuse_post}

include Core_models.Bundle {f_fuse as f_fuse}

include Core_models.Bundle {f_cycle_pre as f_cycle_pre}

include Core_models.Bundle {f_cycle_post as f_cycle_post}

include Core_models.Bundle {f_cycle as f_cycle}

include Core_models.Bundle {f_peekable_pre as f_peekable_pre}

include Core_models.Bundle {f_peekable_post as f_peekable_post}

include Core_models.Bundle {f_peekable as f_peekable}

include Core_models.Bundle {f_intersperse_pre as f_intersperse_pre}

include Core_models.Bundle {f_intersperse_post as f_intersperse_post}

include Core_models.Bundle {f_intersperse as f_intersperse}

include Core_models.Bundle {f_intersperse_with_pre as f_intersperse_with_pre}

include Core_models.Bundle {f_intersperse_with_post as f_intersperse_with_post}

include Core_models.Bundle {f_intersperse_with as f_intersperse_with}

include Core_models.Bundle {f_array_chunks_pre as f_array_chunks_pre}

include Core_models.Bundle {f_array_chunks_post as f_array_chunks_post}

include Core_models.Bundle {f_array_chunks as f_array_chunks}

include Core_models.Bundle {f_map_windows_pre as f_map_windows_pre}

include Core_models.Bundle {f_map_windows_post as f_map_windows_post}

include Core_models.Bundle {f_map_windows as f_map_windows}

include Core_models.Bundle {f_size_hint_pre as f_size_hint_pre}

include Core_models.Bundle {f_size_hint_post as f_size_hint_post}

include Core_models.Bundle {f_size_hint as f_size_hint}

include Core_models.Bundle {f_sum_pre as f_sum_pre}

include Core_models.Bundle {f_sum_post as f_sum_post}

include Core_models.Bundle {f_sum as f_sum}

include Core_models.Bundle {f_product_pre as f_product_pre}

include Core_models.Bundle {f_product_post as f_product_post}

include Core_models.Bundle {f_product as f_product}

include Core_models.Bundle {f_min_by_pre as f_min_by_pre}

include Core_models.Bundle {f_min_by_post as f_min_by_post}

include Core_models.Bundle {f_min_by as f_min_by}

include Core_models.Bundle {f_max_by_pre as f_max_by_pre}

include Core_models.Bundle {f_max_by_post as f_max_by_post}

include Core_models.Bundle {f_max_by as f_max_by}

include Core_models.Bundle {f_min_by_key_pre as f_min_by_key_pre}

include Core_models.Bundle {f_min_by_key_post as f_min_by_key_post}

include Core_models.Bundle {f_min_by_key as f_min_by_key}

include Core_models.Bundle {f_max_by_key_pre as f_max_by_key_pre}

include Core_models.Bundle {f_max_by_key_post as f_max_by_key_post}

include Core_models.Bundle {f_max_by_key as f_max_by_key}

include Core_models.Bundle {f_cmp_pre as f_cmp_pre}

include Core_models.Bundle {f_cmp_post as f_cmp_post}

include Core_models.Bundle {f_cmp as f_cmp}

include Core_models.Bundle {f_cmp_by_pre as f_cmp_by_pre}

include Core_models.Bundle {f_cmp_by_post as f_cmp_by_post}

include Core_models.Bundle {f_cmp_by as f_cmp_by}

include Core_models.Bundle {f_partial_cmp_pre as f_partial_cmp_pre}

include Core_models.Bundle {f_partial_cmp_post as f_partial_cmp_post}

include Core_models.Bundle {f_partial_cmp as f_partial_cmp}

include Core_models.Bundle {f_partial_cmp_by_pre as f_partial_cmp_by_pre}

include Core_models.Bundle {f_partial_cmp_by_post as f_partial_cmp_by_post}

include Core_models.Bundle {f_partial_cmp_by as f_partial_cmp_by}

include Core_models.Bundle {f_eq_pre as f_eq_pre}

include Core_models.Bundle {f_eq_post as f_eq_post}

include Core_models.Bundle {f_eq as f_eq}

include Core_models.Bundle {f_eq_by_pre as f_eq_by_pre}

include Core_models.Bundle {f_eq_by_post as f_eq_by_post}

include Core_models.Bundle {f_eq_by as f_eq_by}

include Core_models.Bundle {f_ne_pre as f_ne_pre}

include Core_models.Bundle {f_ne_post as f_ne_post}

include Core_models.Bundle {f_ne as f_ne}

include Core_models.Bundle {f_lt_pre as f_lt_pre}

include Core_models.Bundle {f_lt_post as f_lt_post}

include Core_models.Bundle {f_lt as f_lt}

include Core_models.Bundle {f_le_pre as f_le_pre}

include Core_models.Bundle {f_le_post as f_le_post}

include Core_models.Bundle {f_le as f_le}

include Core_models.Bundle {f_gt_pre as f_gt_pre}

include Core_models.Bundle {f_gt_post as f_gt_post}

include Core_models.Bundle {f_gt as f_gt}

include Core_models.Bundle {f_ge_pre as f_ge_pre}

include Core_models.Bundle {f_ge_post as f_ge_post}

include Core_models.Bundle {f_ge as f_ge}

include Core_models.Bundle {f_unzip_pre as f_unzip_pre}

include Core_models.Bundle {f_unzip_post as f_unzip_post}

include Core_models.Bundle {f_unzip as f_unzip}

include Core_models.Bundle {f_partition_pre as f_partition_pre}

include Core_models.Bundle {f_partition_post as f_partition_post}

include Core_models.Bundle {f_partition as f_partition}

include Core_models.Bundle {f_is_partitioned_pre as f_is_partitioned_pre}

include Core_models.Bundle {f_is_partitioned_post as f_is_partitioned_post}

include Core_models.Bundle {f_is_partitioned as f_is_partitioned}

include Core_models.Bundle {f_is_sorted_pre as f_is_sorted_pre}

include Core_models.Bundle {f_is_sorted_post as f_is_sorted_post}

include Core_models.Bundle {f_is_sorted as f_is_sorted}

include Core_models.Bundle {f_is_sorted_by_pre as f_is_sorted_by_pre}

include Core_models.Bundle {f_is_sorted_by_post as f_is_sorted_by_post}

include Core_models.Bundle {f_is_sorted_by as f_is_sorted_by}

include Core_models.Bundle {f_is_sorted_by_key_pre as f_is_sorted_by_key_pre}

include Core_models.Bundle {f_is_sorted_by_key_post as f_is_sorted_by_key_post}

include Core_models.Bundle {f_is_sorted_by_key as f_is_sorted_by_key}

include Core_models.Bundle {f_next_chunk_pre as f_next_chunk_pre}

include Core_models.Bundle {f_next_chunk_post as f_next_chunk_post}

include Core_models.Bundle {f_next_chunk as f_next_chunk}

include Core_models.Bundle {f_try_fold_pre as f_try_fold_pre}

include Core_models.Bundle {f_try_fold_post as f_try_fold_post}

include Core_models.Bundle {f_try_fold as f_try_fold}

include Core_models.Bundle {f_try_for_each_pre as f_try_for_each_pre}

include Core_models.Bundle {f_try_for_each_post as f_try_for_each_post}

include Core_models.Bundle {f_try_for_each as f_try_for_each}

include Core_models.Bundle {f_try_find_pre as f_try_find_pre}

include Core_models.Bundle {f_try_find_post as f_try_find_post}

include Core_models.Bundle {f_try_find as f_try_find}

include Core_models.Bundle {f_try_reduce_pre as f_try_reduce_pre}

include Core_models.Bundle {f_try_reduce_post as f_try_reduce_post}

include Core_models.Bundle {f_try_reduce as f_try_reduce}

include Core_models.Bundle {f_try_collect_pre as f_try_collect_pre}

include Core_models.Bundle {f_try_collect_post as f_try_collect_post}

include Core_models.Bundle {f_try_collect as f_try_collect}

include Core_models.Bundle {iter_fold as iter_fold}

include Core_models.Bundle {iter_all as iter_all}

include Core_models.Bundle {iter_any as iter_any}

include Core_models.Bundle {iter_find as iter_find}

include Core_models.Bundle {iter_find_map as iter_find_map}

include Core_models.Bundle {iter_position as iter_position}

include Core_models.Bundle {iter_count as iter_count}

include Core_models.Bundle {iter_nth as iter_nth}

include Core_models.Bundle {iter_last as iter_last}

include Core_models.Bundle {iter_for_each as iter_for_each}

include Core_models.Bundle {iter_reduce as iter_reduce}

include Core_models.Bundle {iter_min as iter_min}

include Core_models.Bundle {iter_max as iter_max}

include Core_models.Bundle {iter_rposition as iter_rposition}

include Core_models.Bundle {iter_advance_by as iter_advance_by}

include Core_models.Bundle {iter_min_by as iter_min_by}

include Core_models.Bundle {iter_max_by as iter_max_by}

include Core_models.Bundle {iter_min_by_key as iter_min_by_key}

include Core_models.Bundle {iter_max_by_key as iter_max_by_key}

include Core_models.Bundle {iter_cmp_by as iter_cmp_by}

include Core_models.Bundle {iter_partial_cmp_by as iter_partial_cmp_by}

include Core_models.Bundle {iter_eq_by as iter_eq_by}

include Core_models.Bundle {iter_unzip as iter_unzip}

include Core_models.Bundle {iter_partition as iter_partition}

include Core_models.Bundle {iter_is_partitioned as iter_is_partitioned}

include Core_models.Bundle {iter_is_sorted_by as iter_is_sorted_by}

include Core_models.Bundle {iter_next_chunk as iter_next_chunk}

include Core_models.Bundle {iter_try_fold as iter_try_fold}

include Core_models.Bundle {iter_try_for_each as iter_try_for_each}

include Core_models.Bundle {t_SeqIter as t_SeqIter}

include Core_models.Bundle {SeqIter as SeqIter}

include Core_models.Bundle {impl__from__iterator as impl}

include Core_models.Bundle {iter_try_find as iter_try_find}

include Core_models.Bundle {iter_try_reduce as iter_try_reduce}

include Core_models.Bundle {iter_try_collect as iter_try_collect}

include Core_models.Bundle {impl_1__from__iterator as impl_1}

include Core_models.Bundle {impl_2__from__iterator as impl_2}
