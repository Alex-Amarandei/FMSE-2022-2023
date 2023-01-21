trait SingletonSpec1
{
    var created: bool
    var instance: SingletonSpec1?

    method getInstance() returns (i: SingletonSpec1)
        requires created == false
        requires instance == null
        modifies this
        ensures created == true
        ensures instance == this
}

class Singleton1 extends SingletonSpec1
{
    constructor () {
        created := false;
        instance := null;
    }

    method getInstance() returns (i: SingletonSpec1)
        requires created == false
        requires instance == null
        modifies this
        ensures created == true
        ensures instance == this
    {
        created := true;
        instance := this;

        return instance;
    }
}

trait SingletonSpec2<T>
{
    const instance: T

    static method getInstance() returns (i: T)
    {
        return instance; // throws error because it implies this exists
    }
}

class Singleton2<T> extends SingletonSpec2<T>
{
    constructor () {}
}