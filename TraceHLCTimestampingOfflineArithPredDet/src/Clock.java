import java.util.Vector;
class Clock
{
    Vector<Integer> pt;
    Clock(){}
    Clock(Vector<Integer> nwTime)
    {
        System.out.println("Parent clock constructor.");
        for(int i=0; i<nwTime.size();i++)
        {
            pt.add(nwTime.get(i));
        }
    }
    void setClock(Vector<Integer> nwTime)
    {
        System.out.println("Setting Parent Pt.");

        pt.set(0,nwTime.get(0));
    }
    void setClockPlusValue(int inc)
    {
        System.out.println("Setting Parent Pt.");

        pt.set(0,pt.get(0)+inc);
    }
    Vector<Integer> getClock()
    {
        System.out.println("Getting Parent Pt.");
        return pt;
    }
    boolean lessThan(Clock pttocomparewith)
    {
        System.out.println("Parent Less Than Invoked. Nothing is done here.");
        return false;
    }
    boolean equalTo(Clock pttocomparewith)
    {
        System.out.println("Parent Equal To Invoked. Nothing is done here.");
        return false;
    }
    void updateLocal(int physicalTime)
    {
        System.out.println("Parent UpdateLocal Invoked. Nothing is done here.");
    }
    void updateMsgRcv(int receiver_time, Clock sndrClk)
    {
        System.out.println("Parent updateMsgRcv Invoked. Nothing is done here.");
    }
}