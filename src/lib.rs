use std::{
    cell::RefCell,
    marker::PhantomData,
    rc::{self, Rc},
    sync::atomic::AtomicPtr,
};


pub fn create_input<T: Default>(_: &str) -> Input<T> {
    Input::default()
}


macro_rules! node {
    (| $($params:ident),* | $body:block) => {
        CachedComputation::new(move |($($params),*,)| $body, ($($params),*,))
    };
}

pub trait F32: Node<Output = f32> + 'static {}
impl<T: Node<Output = f32> + 'static> F32 for T {}


pub fn add(x: impl F32, y: impl F32) -> impl F32 {
    node!(|x, y| { x + y })
}

pub fn mul(x: impl F32, y: impl F32) -> impl F32 {
    node!(|x, y| { x * y })
}

pub fn sin(x: impl F32) -> impl F32 {
    node!(|x| { x.sin() })
}

pub fn pow_f32(x: impl F32, pow: f32) -> impl F32 {
    node!(|x| { x.powf(pow) })
}


#[derive(Clone, Default)]
pub struct Input<T> {
    inner: Rc<RefCell<InputState<T>>>,
}

#[derive(Clone, Default)]
struct InputState<T> {
    value: T,
    invalidator: Invalidator,
}

impl<T> Input<T> {
    pub fn set(&mut self, value: T) {
        let mut inner = self.inner.borrow_mut();

        inner.value = value;
        inner.invalidator.invalidate_all();
    }
}

impl<T: Clone> Node for Input<T> {
    type Output = T;

    fn compute(&mut self) -> Self::Output {
        self.inner.borrow().value.clone()
    }

    fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef) {
        self.inner.borrow_mut().invalidator.invalidate_on_update(subscriber);
    }
}


#[derive(Clone)]
pub struct CachedComputation<F, In, Out> {
    computation: Computation<F, In, Out>,
    cache: Option<Out>,
    invalidator: Invalidator,
}

impl<F, In, Out> CachedComputation<F, In, Out>
where
    F: Fn(In::Output) -> Out + 'static,
    In: Inputs + 'static,
    Out: Clone + 'static,
{
    pub fn new(computation: F, inputs: In) -> Rc<RefCell<Self>> {
        let cached_computation = Self {
            computation: Computation::new(computation, inputs),
            cache: None,
            invalidator: Invalidator::default(),
        };

        let shared = Rc::new(RefCell::new(cached_computation));

        shared.borrow_mut().computation.inputs.subscribe_for_invalidation(Rc::downgrade(&shared) as _);

        // See `<Computation as Compute>::invalidate_on_update`...
        // shared.borrow_mut().computation.invalidate_on_update(Rc::downgrade(&shared) as _);

        shared
    }
}

impl<F, In, Out> Node for CachedComputation<F, In, Out>
where
    F: Fn(In::Output) -> Out + 'static,
    In: Inputs + 'static,
    Out: Clone + 'static,
{
    type Output = Out;

    fn compute(&mut self) -> Self::Output {
        match &self.cache {
            Some(out) => out.clone(),
            None => {
                let out = self.computation.compute();
                self.cache = Some(out.clone());
                out
            }
        }
    }

    fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef) {
        self.invalidator.invalidate_on_update(subscriber);
    }
}

impl<F, In, Out> Invalidate for CachedComputation<F, In, Out> {
    fn invalidate(&mut self) {
        self.cache = None;
        self.invalidator.invalidate_all();
    }
}


#[derive(Clone)]
pub struct Computation<F, In, Out> {
    computation: F,
    inputs: In,
    _phantom: PhantomData<AtomicPtr<Out>>,
}

impl<F, In, Out> Computation<F, In, Out>
where
    F: Fn(In::Output) -> Out,
    In: Inputs,
{
    pub fn new(computation: F, inputs: In) -> Self {
        Self {
            computation,
            inputs,
            _phantom: PhantomData,
        }
    }
}

impl<F, In, Out> Node for Computation<F, In, Out>
where
    F: Fn(In::Output) -> Out,
    In: Inputs,
{
    type Output = Out;

    fn compute(&mut self) -> Self::Output {
        (self.computation)(self.inputs.compute_all())
    }

    fn subscribe_for_invalidation(&mut self, _: InvalidateWeakRef) {
        panic!("`Node` does not support  cache invalidation!");

        // As far as I can see, this *should* work as intended... but might be somewhat confusing.
        // self.inputs.invalidate_on_update(subscriber);
    }
}


pub trait Node {
    type Output;

    fn compute(&mut self) -> Self::Output;
    fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef);
}

impl<T: Node> Node for Rc<RefCell<T>> {
    type Output = T::Output;

    fn compute(&mut self) -> Self::Output {
        self.borrow_mut().compute()
    }

    fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef) {
        self.borrow_mut().subscribe_for_invalidation(subscriber);
    }
}


pub type InvalidateWeakRef = rc::Weak<RefCell<dyn Invalidate>>;


pub trait Invalidate {
    fn invalidate(&mut self);
}


pub trait Inputs {
    type Output;

    fn compute_all(&mut self) -> Self::Output;
    fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef);
}

impl Inputs for () {
    type Output = ();

    fn compute_all(&mut self) -> Self::Output {
        ()
    }

    fn subscribe_for_invalidation(&mut self, _: InvalidateWeakRef) {
        // Do nothing...
    }
}

macro_rules! inputs {
    (@generate $($prev:ident)* ; ) => {};

    (@generate $($prev:ident)* ; $current:ident $($next:ident)*) => {
        impl<$($prev,)* $current> Inputs for ($($prev,)* $current,)
        where
            $($prev: Node,)*
            $current: Node,
        {
            type Output = ($($prev::Output,)* $current::Output,);

            #[allow(non_snake_case)]
            fn compute_all(&mut self) -> Self::Output {
                let ($($prev,)* $current,) = self;
                ($($prev.compute(),)* $current.compute(),)
            }

            #[allow(non_snake_case)]
            fn subscribe_for_invalidation(&mut self, subscriber: InvalidateWeakRef) {
                let ($($prev,)* $current,) = self;
                $($prev.subscribe_for_invalidation(subscriber.clone());)*
                $current.subscribe_for_invalidation(subscriber);
            }
        }

        inputs!(@generate $($prev)* $current ; $($next)*);
    };

    ($($generics:ident),+ $(,)?) => {
        inputs!(@generate ; $($generics)*);
    };
}

inputs!(A, B, C, D);


#[derive(Clone, Default)]
struct Invalidator {
    subscribers: Vec<InvalidateWeakRef>,
}

impl Invalidator {
    pub fn invalidate_on_update(&mut self, subscriber: InvalidateWeakRef) {
        self.subscribers.push(subscriber);
    }

    pub fn invalidate_all(&mut self) {
        self.subscribers
            .retain(|sub| sub.upgrade().map(|sub| sub.borrow_mut().invalidate()).is_some())
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn example() {
        let mut x1 = create_input("x1");
        let mut x2 = create_input("x2");
        let mut x3 = create_input("x3");

        let mut graph = add(
            x1.clone(),
            mul(
                x2.clone(),
                sin(add(
                    x2.clone(),
                    pow_f32(x3.clone(), 3f32),
                )),
            ),
        );

        x1.set(1f32);
        x2.set(2f32);
        x3.set(3f32);

        let result = graph.compute();

        println!("Graph output = {:.6}", result);
        assert_eq!(round(result, 5), -0.32727);

        x1.set(2f32);
        x2.set(3f32);
        x3.set(4f32);

        let result = graph.compute();

        println!("Graph output = {:.6}", result);
        assert_eq!(round(result, 5), -0.56656);
    }

    fn round(x: f32, precision: u32) -> f32 {
        let m = 10i32.pow(precision) as f32;
        (x * m).round() / m
    }
}
