//! Dataflow analyses are built upon some interpretation of the
//! bitvectors attached to each basic block, represented via a
//! zero-sized structure.

mod borrowed_locals;
mod initialized;
mod liveness;
mod logically_parallel_tasks;
mod storage_liveness;
mod syncable_tasks;

pub use self::borrowed_locals::borrowed_locals;
pub use self::borrowed_locals::MaybeBorrowedLocals;
pub use self::initialized::{
    DefinitelyInitializedPlaces, EverInitializedPlaces, MaybeInitializedPlaces,
    MaybeUninitializedPlaces,
};
pub use self::liveness::MaybeLiveLocals;
pub use self::liveness::MaybeTransitiveLiveLocals;
pub use self::liveness::TransferFunction as LivenessTransferFunction;
pub use self::storage_liveness::{MaybeRequiresStorage, MaybeStorageDead, MaybeStorageLive};
pub use self::syncable_tasks::{
    definitely_synced_tasks, maybe_synced_tasks, DefinitelySyncableTasks, DefinitelySyncedTasks,
    MaybeSyncableTasks, MaybeSyncedTasks,
};
