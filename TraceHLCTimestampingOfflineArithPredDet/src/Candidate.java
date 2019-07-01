class Candidate
{
    Clock startClock;
    Clock endClock;
    String color;
    Candidate(Clock startClk, Clock endClk)
    {
        startClock=startClk;
        endClock=endClk;
        color="red";
    }
    Clock getStartClock()
    {
        return startClock;
    }
    Clock getEndClock()
    {
        return endClock;
    }
    void setStartClock(Clock startClk)
    {
        startClock=startClk;
    }
    void setEndClock(Clock endClk)
    {
        endClock=endClk;
    }
    String getColor()
    {
        return color;
    }
    void setColor(String nwColor)
    {
        color=nwColor;
    }
}